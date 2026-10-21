"""Compatibility and failure tests for individual native-check successes."""
import json
import os
from pathlib import Path
import tempfile
import unittest

from lean_ci.execution.state import (Progress, check_binding, digest, file_hash, module_identity,
    read_json, InputDrift, ReflectionGraph, TemporalInputs, valid_receipt, write_json)
from lean_ci.project.source import lean_imports, module_path


def native_fixture(root, name, dep_hash='0123456789abcdef', payload=b'compiled'):
    relative = module_path(name).with_suffix('')
    outputs = {'o': ['0' * 16 + suffix for suffix in ('.olean', '.olean.server', '.olean.private')],
               'i': '0' * 16 + '.ilean', 'r': '0' * 16 + '.ir',
               'rs': '0' * 16 + '.ir.sig', 'c': '0' * 16 + '.c', 'm': True}
    for suffix in ('.olean', '.olean.server', '.olean.private', '.ilean', '.ir', '.ir.sig', '.c'):
        folder = '.lake/build/ir' if suffix == '.c' else '.lake/build/lib/lean'
        target = root / folder / (str(relative) + suffix)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(payload + suffix.encode())
    source = root / module_path(name)
    imports = lean_imports(source.read_text()) if source.is_file() else []
    write_json(root / '.lake/build/lib/lean' / (str(relative) + '.ilean'),
               {'version': 5, 'module': name,
                'directImports': [[n, False, False, False] for n in imports]})
    write_json(root / '.lake/build/lib/lean' / (str(relative) + '.trace'),
               {'schemaVersion': '2025-09-10', 'synthetic': True, 'inputs': [],
                'outputs': outputs, 'depHash': dep_hash, 'log': []})


def receipt(command, cwd=None, **changes):
    return {'state': 'completed', 'command': list(command), 'cwd': str(cwd or Path.cwd()),
            'exit_code': 0, 'guard_failure': None, 'owned_group_gone': True, **changes}


class ProgressTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='aglib-check-progress-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'root'
        self.root.mkdir()
        (self.root / 'Aglib').mkdir()
        (self.root / 'Aglib/Base.lean').write_text('def x := 1\n')
        (self.root / 'checker.py').write_text('actual checker\n')
        (self.root / 'lakefile.toml').write_text('weak.argument = true\n')
        native_fixture(self.root, 'Aglib.Base')
        self.progress = Progress(Path(self.temp.name) / 'progress')
        self.calls = 0

    def binding(self):
        return check_binding(self.root, 'builtin', ['Aglib.Base'],
                             ['lake', '--no-build', 'lint', '--builtin-only', 'Aglib.Base'],
                             ['checker.py', 'lakefile.toml'], raw_paths=['Aglib/Base.lean'],
                             toolchain={'lean': 'pinned actual compiler'})

    def execute(self):
        self.calls += 1
        command = self.binding()['arguments']
        return receipt(command, self.root), command


    def test_build_trace_alone_is_not_lint_success_and_matching_success_reuses(self):
        self.assertEqual(self.progress.run(self.binding, self.execute)['mode'], 'performed')
        self.assertEqual(self.progress.run(self.binding, self.execute)['mode'], 'reused')
        self.assertEqual(self.calls, 1)
        self.assertTrue(module_identity(self.root, 'Aglib.Base')['outputs'])

    def test_changed_dep_hash_output_checker_raw_comment_and_weak_args_each_rerun(self):
        self.progress.run(self.binding, self.execute)
        native_fixture(self.root, 'Aglib.Base', dep_hash='f' * 16)
        self.assertEqual(self.progress.run(self.binding, self.execute)['mode'], 'performed')
        (self.root / '.lake/build/lib/lean/Aglib/Base.olean.private').write_bytes(b'different actual output')
        self.assertEqual(self.progress.run(self.binding, self.execute)['mode'], 'performed')
        (self.root / 'checker.py').write_text('new actual checker\n')
        self.assertEqual(self.progress.run(self.binding, self.execute)['mode'], 'performed')
        (self.root / 'Aglib/Base.lean').write_text('-- style-relevant raw comment\ndef x := 1\n')
        self.assertEqual(self.progress.run(self.binding, self.execute)['mode'], 'performed')
        (self.root / 'lakefile.toml').write_text('weak.argument = false\n')
        self.assertEqual(self.progress.run(self.binding, self.execute)['mode'], 'performed')
        self.assertEqual(self.calls, 6)

    def test_missing_corrupt_failed_and_wrong_command_records_rerun_actual_check(self):
        for corrupt in ('invalid JSON', {'status': 'running'}, {'status': 'success'}, None):
            self.progress.run(self.binding, self.execute)
            path = self.progress.directory / (digest(self.binding()) + '.json')
            if corrupt is None:
                value = read_json(path)
                value['receipt']['command'] = ['true']
                value['executed_command'] = ['true']
                write_json(path, value)
            elif isinstance(corrupt, str):
                path.write_text(corrupt)
            else:
                write_json(path, corrupt)
            with self.subTest(corrupt=corrupt):
                self.assertEqual(self.progress.run(self.binding, self.execute)['mode'], 'performed')

    def test_only_exit_zero_guard_null_closed_group_receipts_can_create_success(self):
        for changes in ({'exit_code': 1}, {'exit_code': False}, {'guard_failure': 'RSS'},
                        {'owned_group_gone': False}, {'state': 'running'}):
            def execute():
                args = self.binding()['arguments']
                return receipt(args, self.root, **changes), args
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.progress.run(self.binding, execute)
        self.assertEqual(list(self.progress.directory.iterdir()), [])
        self.assertFalse(valid_receipt({'exit_code': 0}))

    def test_drift_during_execution_does_not_record_success(self):
        def execute():
            outcome = self.execute()
            (self.root / 'Aglib/Base.lean').write_text('def x := 2\n')
            return outcome
        with self.assertRaisesRegex(ValueError, 'drifted'):
            self.progress.run(self.binding, execute)
        self.assertEqual(list(self.progress.directory.iterdir()), [])

    def test_later_failure_preserves_earlier_individual_success(self):
        first = self.progress.run(self.binding, self.execute)
        def other_binding():
            value = self.binding()
            value['kind'] = 'declaration'
            return value
        def failed():
            raise RuntimeError('later declaration failure')
        with self.assertRaises(RuntimeError):
            self.progress.run(other_binding, failed)
        self.assertEqual(self.progress.lookup(self.binding()), first['success'])
        self.assertEqual(self.progress.run(self.binding, self.execute)['mode'], 'reused')

    def test_unknown_trace_schema_or_missing_output_is_not_usable_build_identity(self):
        trace = self.root / '.lake/build/lib/lean/Aglib/Base.trace'
        value = json.loads(trace.read_text())
        value['schemaVersion'] = 'unknown'
        write_json(trace, value)
        with self.assertRaisesRegex(ValueError, 'Unsupported native trace'):
            self.binding()
        native_fixture(self.root, 'Aglib.Base')
        (self.root / '.lake/build/lib/lean/Aglib/Base.olean').unlink()
        with self.assertRaises(OSError):
            self.binding()

    def test_legacy_nonmodule_trace_hashes_its_actual_smaller_output_set(self):
        trace = self.root / '.lake/build/lib/lean/Aglib/Base.trace'
        value = read_json(trace)
        value['outputs']['m'] = False
        value['outputs']['o'] = value['outputs']['o'][:1]
        del value['outputs']['r']
        del value['outputs']['rs']
        write_json(trace, value)
        result = module_identity(self.root, 'Aglib.Base')
        self.assertEqual(len(result['outputs']), 3)
        self.assertIn('.lake/build/lib/lean/Aglib/Base.olean', result['outputs'])


class ReflectionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='aglib-reflection-inputs-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'repo'
        self.root.mkdir()
        for name, text in [('Aglib.Base', 'module\nmeta import all Aglib.Imported\ndef x := 1\n'),
                           ('Aglib.Imported', 'module\ndef hidden := 1\n'),
                           ('Aglib.Unrelated', 'module\ndef unrelated := 1\n'), ('Init', 'module\n')]:
            path = self.root / module_path(name)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            native_fixture(self.root, name)
        metadata = self.root / '.lake/build/lib/lean/Aglib/Base.ilean'
        value = read_json(metadata)
        value['directImports'][0][1:] = [True, True, True]
        write_json(metadata, value)
        self.toolchain = {'installation': str(Path(self.temp.name) / 'compiler'), 'lean': 'actual pinned binary'}
        self.progress = Progress(Path(self.temp.name) / 'progress')
        self.calls = 0

    def graph(self, paths=None):
        return ReflectionGraph(self.root, paths or [str(self.root / '.lake/build/lib/lean')], self.toolchain)

    def namespace_fixture(self, name='Dep.Child'):
        dependency = self.root / '.lake/packages/dependency'
        source = dependency / module_path(name)
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text('module\ndef imported := 1\n')
        native_fixture(dependency, name)
        (self.root / 'Aglib/Base.lean').write_text('module\nimport ' + name + '\ndef x := 1\n')
        native_fixture(self.root, 'Aglib.Base')
        return self.root / '.lake/build/lib/lean', dependency / '.lake/build/lib/lean'

    def bound(self, graph):
        return {'schema': 1, 'kind': 'audit', 'arguments': ['audit', 'Aglib.Base'],
                'native': module_identity(self.root, 'Aglib.Base', graph.hash_file),
                'reflective_imports': graph.closure(['Aglib.Base'])}

    def execute(self):
        self.calls += 1
        args = ['audit', 'Aglib.Base']
        return receipt(args, self.root), args

    def test_imported_private_body_change_invalidates_success_with_unchanged_own_build_identity(self):
        graph = self.graph()
        own = module_identity(self.root, 'Aglib.Base')
        first = self.progress.run(lambda: self.bound(graph), self.execute)
        private = self.root / '.lake/build/lib/lean/Aglib/Imported.olean.private'
        private.write_bytes(b'changed imported private proof; public ABI unchanged')
        self.assertEqual(module_identity(self.root, 'Aglib.Base'), own)
        again = self.graph()
        second = self.progress.run(lambda: self.bound(again), self.execute)
        self.assertEqual(second['mode'], 'performed')
        self.assertNotEqual(first['success']['key'], second['success']['key'])
        self.assertEqual(self.calls, 2)

    def test_unrelated_repair_preserves_success_and_shared_hashing_is_deduplicated(self):
        graph = self.graph()
        first = self.progress.run(lambda: self.bound(graph), self.execute)
        hashes = graph.hash_count
        self.assertIsNotNone(graph.closure(['Aglib.Imported']))
        self.assertEqual(graph.hash_count, hashes)
        (self.root / '.lake/build/lib/lean/Aglib/Unrelated.olean.private').write_bytes(b'unrelated repair')
        again = self.graph()
        second = self.progress.run(lambda: self.bound(again), self.execute)
        self.assertEqual(second['mode'], 'reused')
        self.assertEqual(first['success']['key'], second['success']['key'])
        self.assertEqual(self.calls, 1)

    def test_bad_version_module_flags_missing_or_unknown_import_metadata_disables_reuse(self):
        metadata = self.root / '.lake/build/lib/lean/Aglib/Imported.ilean'
        original = metadata.read_text()
        for change in ('version', 'module', 'flags', 'missing', 'unknown'):
            value = json.loads(original)
            if change == 'version':
                value['version'] = 4
            elif change == 'module':
                value['module'] = 'Wrong.Module'
            elif change == 'flags':
                value['directImports'] = [['Init', 'false', False, False]]
            elif change == 'unknown':
                value['directImports'] = [['Lean.UnknownWorkspaceImport', False, False, False]]
            if change == 'missing':
                metadata.unlink()
            else:
                write_json(metadata, value)
            with self.subTest(change=change):
                self.assertIsNone(self.graph().closure(['Aglib.Base']))
            metadata.write_text(original)

    def test_workspace_init_shadow_is_bound_instead_of_skipped_by_namespace(self):
        graph = self.graph()
        before = graph.closure(['Aglib.Base'])
        self.assertTrue(graph.nodes['Init']['owner'].startswith('workspace:'))
        (self.root / '.lake/build/lib/lean/Init.olean.private').write_bytes(b'changed real workspace shadow')
        self.assertNotEqual(self.graph().closure(['Aglib.Base']), before)

    def test_changed_and_restored_imported_output_during_check_never_records_success(self):
        graph = self.graph()
        private = self.root / '.lake/build/lib/lean/Aglib/Imported.olean.private'
        old_bytes, old_stat = private.read_bytes(), private.stat()
        def execute():
            private.write_bytes(b'transient imported private proof')
            private.write_bytes(old_bytes)
            os.utime(private, ns=(old_stat.st_atime_ns, old_stat.st_mtime_ns))
            return self.execute()
        with self.assertRaises(InputDrift):
            self.progress.run(lambda: self.bound(graph), execute)
        self.assertEqual(list(self.progress.directory.iterdir()), [])

    def test_first_namespace_directory_or_root_file_blocks_later_complete_module(self):
        high, low = self.namespace_fixture()
        first_graph = self.graph([high, low])
        first = self.progress.run(lambda: self.bound(first_graph), self.execute)
        self.assertEqual(first['mode'], 'performed')
        for shadow in ('directory', 'root-file'):
            path = high / ('Dep' if shadow == 'directory' else 'Dep.olean')
            path.mkdir() if shadow == 'directory' else path.write_bytes(b'namespace marker')
            graph = self.graph([high, low])
            with self.subTest(shadow=shadow):
                self.assertIsNone(graph.closure(['Aglib.Base']))
                self.assertNotIn('Dep.Child', graph.nodes)
                def checker():
                    raise RuntimeError('Native checker cannot read the selected first-root child')
                with self.assertRaises(RuntimeError):
                    self.progress.run(lambda: self.bound(graph), checker, reuse=False)
            path.rmdir() if shadow == 'directory' else path.unlink()
        self.assertEqual(len(list(self.progress.directory.glob('*.json'))), 1)

    def test_plain_namespace_file_without_olean_does_not_shadow_later_module(self):
        high, low = self.namespace_fixture()
        (high / 'Dep').write_bytes(b'not a namespace directory')
        graph = self.graph([high, low])
        self.assertIsNotNone(graph.closure(['Aglib.Base']))
        self.assertIn('.lake/packages/dependency', graph.nodes['Dep.Child']['owner'])

    def test_quoted_root_component_is_one_native_namespace(self):
        high, low = self.namespace_fixture('«Dep.Root».Child')
        self.assertIsNotNone(self.graph([high, low]).closure(['Aglib.Base']))
        (high / 'Dep.Root').mkdir()
        self.assertIsNone(self.graph([high, low]).closure(['Aglib.Base']))

    def test_transient_shadow_in_every_preceding_entry_cannot_save_success(self):
        high, low = self.namespace_fixture()
        middle = self.root / '.lake/middle/lib/lean'
        middle.mkdir(parents=True)
        for index, (library, kind) in enumerate(((high, 'directory'), (middle, 'directory'),
                                                (high, 'root-file'), (middle, 'root-file'))):
            graph = self.graph([high, middle, low])
            progress = Progress(self.progress.directory / str(index))
            def execute(library=library, kind=kind):
                path = library / ('Dep' if kind == 'directory' else 'Dep.olean')
                if kind == 'directory':
                    path.mkdir()
                    (path / 'Child.olean').write_bytes(b'temporary alternative proof')
                    (path / 'Child.olean').unlink()
                    path.rmdir()
                else:
                    path.write_bytes(b'temporary namespace marker')
                    path.unlink()
                return self.execute()
            with self.subTest(library=library, kind=kind), self.assertRaises(InputDrift):
                progress.run(lambda: self.bound(graph), execute)
            self.assertEqual(list(progress.directory.glob('*.json')), [])

    def test_removing_and_restoring_an_earlier_complete_namespace_cannot_save_success(self):
        high, low = self.namespace_fixture()
        source = self.root / 'Dep/Child.lean'
        source.parent.mkdir()
        source.write_text('module\ndef earlier := 2\n')
        native_fixture(self.root, 'Dep.Child')
        graph = self.graph([high, low])
        self.assertIsNotNone(graph.closure(['Aglib.Base']))
        self.assertEqual(graph.nodes['Dep.Child']['owner'], 'workspace:.lake/build/lib/lean')
        def execute():
            namespace = high / 'Dep'
            moved = high.parent / 'temporarily-removed-Dep'
            namespace.rename(moved)
            moved.rename(namespace)
            return self.execute()
        with self.assertRaises(InputDrift):
            self.progress.run(lambda: self.bound(graph), execute)
        self.assertEqual(list(self.progress.directory.glob('*.json')), [])

    def test_transient_creation_of_a_previously_missing_search_entry_is_observed(self):
        high, low = self.namespace_fixture()
        missing = self.root / '.lake/new-entry/lib/lean'
        graph = self.graph([missing, high, low])
        def execute():
            namespace = missing / 'Dep'
            namespace.mkdir(parents=True)
            namespace.rmdir()
            missing.rmdir()
            missing.parent.rmdir()
            missing.parent.parent.rmdir()
            return self.execute()
        with self.assertRaises(InputDrift):
            self.progress.run(lambda: self.bound(graph), execute)
        self.assertEqual(list(self.progress.directory.glob('*.json')), [])

    def policy_binding(self, graph):
        value = check_binding(self.root, 'declaration', ['Aglib.Base'], ['audit', 'Aglib.Base'],
                              ['scripts/nolints.json'], hash_file=graph.hash_file)
        value['reflective_imports'] = graph.closure(['Aglib.Base'])
        return value

    def test_transient_optional_policy_appearance_and_removal_never_records_success(self):
        (self.root / 'scripts').mkdir()
        graph = self.graph()
        def execute():
            policy = self.root / 'scripts/nolints.json'
            policy.write_text('[["docBlame", "Aglib.badDefinition"]]\n')
            policy.unlink()
            return self.execute()
        with self.assertRaises(InputDrift):
            self.progress.run(lambda: self.policy_binding(graph), execute)
        self.assertEqual(list(self.progress.directory.glob('*.json')), [])

    def test_absent_policy_compatibility_key_survives_unrelated_parent_changes_between_runs(self):
        scripts = self.root / 'scripts'
        scripts.mkdir()
        graph = self.graph()
        first = self.progress.run(lambda: self.policy_binding(graph), self.execute)
        self.assertEqual(first['success']['binding']['raw_inputs'], {'scripts/nolints.json': None})
        (scripts / 'unrelated.txt').write_text('unrelated repair\n')
        (scripts / 'unrelated.txt').unlink()
        again = self.graph()
        second = self.progress.run(lambda: self.policy_binding(again), self.execute)
        self.assertEqual(second['mode'], 'reused')
        self.assertEqual(first['success']['key'], second['success']['key'])

    def test_compiler_runtime_observations_are_shared_with_reflection_check_success(self):
        compiler = Path(self.temp.name) / 'compiler-runtime'
        compiler.write_bytes(b'original compiler')
        observations = TemporalInputs()
        original = observations.hash_file(compiler)
        graph = ReflectionGraph(self.root, [str(self.root / '.lake/build/lib/lean')],
                                self.toolchain, observations=observations)
        def execute():
            compiler.write_bytes(b'transient compiler')
            compiler.write_bytes(b'original compiler')
            return self.execute()
        with self.assertRaises(InputDrift):
            self.progress.run(lambda: self.bound(graph), execute)
        self.assertEqual(list(self.progress.directory.glob('*.json')), [])
        self.assertEqual(file_hash(compiler), original)
        self.assertIs(graph.observations, observations)

    def test_retargeted_and_restored_search_path_symlink_cannot_save_success(self):
        high, low = self.namespace_fixture()
        dependency = low.parents[3]
        alias = self.root / '.lake/packages/alias'
        alias.symlink_to(dependency, target_is_directory=True)
        alternative = self.root / '.lake/packages/alternative'
        alternative.mkdir()
        graph = self.graph([high, alias / '.lake/build/lib/lean'])
        def execute():
            alias.unlink()
            alias.symlink_to(alternative, target_is_directory=True)
            alias.unlink()
            alias.symlink_to(dependency, target_is_directory=True)
            return self.execute()
        with self.assertRaises(InputDrift):
            self.progress.run(lambda: self.bound(graph), execute)
        self.assertEqual(list(self.progress.directory.glob('*.json')), [])


class TemporalInputTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='aglib-temporal-inputs-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def test_present_file_parent_cache_writes_do_not_invalidate_observed_file(self):
        source = self.root / 'input'
        source.write_bytes(b'actual input')
        observations = TemporalInputs()
        first = observations.hash_file(source)
        (self.root / 'unrelated.hash').write_bytes(b'normal cache sidecar')
        (self.root / 'unrelated.hash').unlink()
        observations.assert_stable()
        self.assertEqual(observations.hash_file(source), first)
        self.assertEqual(observations.hash_count, 1)

    def test_retargeted_and_restored_input_symlink_is_observed(self):
        source, alternative, link = (self.root / n for n in ('source', 'alternative', 'link'))
        source.write_bytes(b'original input')
        alternative.write_bytes(b'alternative input')
        link.symlink_to(source)
        observations = TemporalInputs()
        observations.hash_file(link)
        link.unlink()
        link.symlink_to(alternative)
        link.unlink()
        link.symlink_to(source)
        with self.assertRaises(InputDrift):
            observations.assert_stable()

    def test_absent_input_observer_preserves_none_key_but_catches_transient_appearance(self):
        source = self.root / 'optional-policy.json'
        observations = TemporalInputs()
        self.assertIsNone(observations.optional_hash(source))
        source.write_text('temporary suppression')
        source.unlink()
        with self.assertRaises(InputDrift):
            observations.assert_stable()
        self.assertIsNone(TemporalInputs().optional_hash(source))


if __name__ == '__main__':
    unittest.main()
