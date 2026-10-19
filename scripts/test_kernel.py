"""Controller tests with fake artifacts and markers; never execute Lean."""
from contextlib import redirect_stdout
import io
import json
import os
import shutil
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_kernel as kernel


class KernelTests(unittest.TestCase):
    def fixture(self, temporary):
        root, prefix = Path(temporary) / 'root', Path(temporary) / 'toolchain'
        sources = {Path('Aglib.lean'), Path('Aglib/One.lean'), Path('AglibTest.lean')}
        for source in sources:
            (root / source).parent.mkdir(parents=True, exist_ok=True)
            (root / source).write_text('module\n')
            output = root / '.lake/build/lib/lean' / source.with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(b'fake module')
        self.imports, self.external = {}, {}
        (root / 'lean-toolchain').write_text('fixed toolchain')
        (root / 'lakefile.toml').write_text('name = \"Fixture\"\n')
        (root / 'lake-manifest.json').write_text('{\"packages\": []}')
        for name in ['lib/lean/LeanChecker.olean', 'src/lean/LeanChecker.lean', 'bin/lean', 'lib/libleanshared.dylib']:
            (prefix / name).parent.mkdir(parents=True, exist_ok=True)
            (prefix / name).write_text('fixed checker')
        return root, prefix, sources

    def patched(self, prefix, sources):
        from contextlib import ExitStack
        stack = ExitStack()
        stack.enter_context(patch.object(kernel, 'check_inventory', return_value=[]))
        stack.enter_context(patch.object(kernel, 'expected_sources', return_value=sources))
        environment = {'lean': str(prefix / 'bin/lean'),
            'LEAN_PATH': os.pathsep.join(str(artifact.parents[len(kernel.module_path(name).parts) - 1])
                for name, (source, artifact) in self.external.items()),
            'LEAN_SRC_PATH': os.pathsep.join(str(source.parents[len(kernel.module_path(name).parts) - 1])
                for name, (source, artifact) in self.external.items() if source is not None)}
        stack.enter_context(patch.object(kernel, 'lake_environment', return_value=environment))
        stack.enter_context(patch.object(kernel.subprocess, 'check_output', return_value=str(prefix)))
        stack.enter_context(patch.object(kernel.os, 'cpu_count', return_value=8))
        stack.enter_context(patch.object(kernel, 'import_graph', side_effect=self.metadata))
        stack.enter_context(redirect_stdout(io.StringIO()))
        return stack

    def metadata(self, root, prefix, lean, environment, directory, modules):
        pending, graph = list(modules) + ['LeanChecker'], {}
        while pending:
            name = pending.pop()
            if name in graph:
                continue
            if name == 'LeanChecker':
                source, artifact = prefix / 'src/lean/LeanChecker.lean', prefix / 'lib/lean/LeanChecker.olean'
            elif name in self.external:
                source, artifact = self.external[name]
            else:
                source = root / kernel.module_path(name)
                artifact = root / '.lake/build/lib/lean' / kernel.module_path(name).with_suffix('.olean')
            imports = self.imports.get(name, [])
            artifacts = [path for path in [artifact, Path(str(artifact) + '.server'),
                                          Path(str(artifact) + '.private')] if path.is_file()]
            graph[name] = {'module': name, 'source': str(source) if source is not None else None,
                           'artifacts': list(map(str, artifacts)), 'imports': imports}
            pending.extend(imports)
        return graph

    def record(self, directory, name):
        summary = json.loads((directory / 'coverage.json').read_text())
        return directory / summary['module_records'][name]

    def guarded(self, calls, failures=()):
        def fake(command, **kwargs):
            names = kwargs['env']['AGLIB_KERNEL_MODULES'].split('\n')
            calls.append(names)
            self.assertNotIn('--run', command)
            self.assertIn('-j' + str(len(names)), command)
            self.assertEqual(kwargs['env']['LEAN_NUM_THREADS'], str(len(names)))
            reason = 'owned process group exceeded RSS cutoff' if len(calls) in failures else None
            code = 137 if reason else 0
            if not reason:
                for name in names:
                    count = 2 if name == 'Aglib.One' else 0
                    kwargs['stdout'].write(f'AGLIB_KERNEL_CHECKED {name} {count}\n')
            kernel.write_json(kwargs['receipt'], {'command': command, 'limits': kwargs['budget'],
                'exit_code': -15 if reason else 0, 'guard_failure': reason, 'owned_group_gone': True})
            return code
        return fake

    def test_driver_exact_tasks_join_before_markers_without_upstream_main(self):
        self.assertIn('import LeanChecker', kernel.DRIVER)
        self.assertIn('IO.asTask (checkOne name)', kernel.DRIVER)
        self.assertIn('replayFromImports name', kernel.CHECK_ONE)
        self.assertIn('parts[parts.size - 1].1.constNames.size', kernel.CHECK_ONE)
        self.assertLess(kernel.DRIVER.index('for (name, task) in tasks'),
                        kernel.DRIVER.index('unless errors.isEmpty'))
        self.assertLess(kernel.DRIVER.index('unless errors.isEmpty'),
                        kernel.DRIVER.index('AGLIB_KERNEL_CHECKED'))
        self.assertNotIn('def main', kernel.DRIVER)
        self.assertNotIn('--run', kernel.DRIVER)
        self.assertNotIn('replayFromFresh', kernel.DRIVER)

    def test_probe_resume_preserves_old_profile_and_covers_exact_set(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
            calls = []
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)):
                kernel.replay(root, directory, only='Aglib.One', batch_size=1)
                probe = json.loads((directory / 'probe.json').read_text())
                original_path = directory / probe['module_records']['Aglib.One']
                original = original_path.read_bytes()
                kernel.replay(root, directory, batch_size=2)
                self.assertEqual(calls, [['Aglib.One'], ['Aglib', 'AglibTest']])
                self.assertEqual(json.loads((directory / 'coverage.json').read_text())['covered_modules'], 3)
                self.assertEqual(original_path.read_bytes(), original)
                self.assertNotIn('limits', json.loads((directory / 'basis.json').read_text()))
                (root / 'Aglib/One.lean').write_text('changed source')
                basis_before = (directory / 'basis.json').read_bytes()
                kernel.replay(root, directory, batch_size=4)
                self.assertEqual(calls[-1], ['Aglib.One'])
                self.assertEqual((directory / 'basis.json').read_bytes(), basis_before)
                self.assertEqual(original_path.read_bytes(), original)
                self.assertNotEqual(self.record(directory, 'Aglib.One').read_bytes(), original)

    def test_resource_failure_accepts_none_of_failed_batch_then_retries_smaller(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
            calls = []
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls, [1])):
                kernel.replay(root, directory, batch_size=4)
            self.assertEqual([len(batch) for batch in calls], [3, 1, 2])
            records = [json.loads(path.read_text()) for path in directory.glob('module-*.json')]
            self.assertEqual(len(records), 3)
            self.assertTrue(all(record['resource'] != 'batch-0000.resource.json' for record in records))

    def test_orphan_attempt_logs_and_resources_are_preserved_on_resume(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
            directory.mkdir()
            orphan_log = directory / 'batch-0000.log'; orphan_log.write_text('original interrupted log')
            orphan_resource = directory / 'batch-0001.resource.json'
            orphan_resource.write_text('original interrupted resource')
            calls = []
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)):
                kernel.replay(root, directory, batch_size=4)
            self.assertEqual(orphan_log.read_text(), 'original interrupted log')
            self.assertEqual(orphan_resource.read_text(), 'original interrupted resource')
            self.assertTrue((directory / 'batch-0002.json').is_file())
            self.assertFalse((directory / 'batch-0000.json').exists())
            self.assertFalse((directory / 'batch-0001.json').exists())

    def test_malformed_markers_and_proof_failures_are_not_resource_backoff(self):
        for text in ['AGLIB_KERNEL_CHECKED Aglib 0\n',
                     'AGLIB_KERNEL_CHECKED Aglib 0\nAGLIB_KERNEL_CHECKED Aglib 0\n',
                     'AGLIB_KERNEL_CHECKED Other 0\n']:
            with self.assertRaises(RuntimeError):
                kernel.parse_markers(text, ['Aglib', 'Aglib.One'])
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
            calls = []
            def reject(command, **kwargs):
                calls.append(command)
                kwargs['stdout'].write('while replaying declaration: invalid proof\n')
                kernel.write_json(kwargs['receipt'], {'exit_code': 1, 'guard_failure': None,
                                                      'owned_group_gone': True})
                return 1
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=reject):
                with self.assertRaisesRegex(RuntimeError, 'batch failed'):
                    kernel.replay(root, directory, batch_size=4)
            self.assertEqual(len(calls), 1)
            self.assertFalse(list(directory.glob('module-*.json')))

    def test_source_change_after_zero_exit_prevents_acceptance(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
            base = self.guarded([])
            def mutate(command, **kwargs):
                code = base(command, **kwargs)
                (root / 'Aglib/One.lean').write_text('changed after replay')
                return code
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=mutate):
                with self.assertRaisesRegex(RuntimeError, 'basis changed during'):
                    kernel.replay(root, directory, batch_size=4)
            self.assertFalse(list(directory.glob('module-*.json')))

    def test_unrelated_reuse_and_source_dependency_invalidation(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
            self.imports['Aglib'] = ['Aglib.One']
            calls = []
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)):
                kernel.replay(root, directory, batch_size=4)
                old = self.record(directory, 'AglibTest').read_bytes()
                (root / 'Aglib/One.lean').write_text('dirty imported source; artifact unchanged')
                kernel.replay(root, directory, batch_size=4)
                self.assertEqual(calls[-1], ['Aglib', 'Aglib.One'])
                self.assertEqual(self.record(directory, 'AglibTest').read_bytes(), old)
                self.assertEqual(json.loads((directory / 'coverage.json').read_text())['reused_modules'], 1)

    def test_external_dependency_source_and_all_artifact_facets_invalidate_dependents(self):
        for changed in ['source', '', '.server', '.private', 'remove-private', 'ir', 'ir.sig']:
            with self.subTest(changed=changed), tempfile.TemporaryDirectory() as temporary:
                root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
                source = root / '.lake/packages/dep/Dep.lean'
                artifact = root / '.lake/packages/dep/.lake/build/lib/lean/Dep.olean'
                source.parent.mkdir(parents=True); source.write_text('external source')
                artifact.parent.mkdir(parents=True); artifact.write_text('exported')
                Path(str(artifact) + '.server').write_text('server')
                Path(str(artifact) + '.private').write_text('private')
                artifact.with_suffix('.ir').write_text('IR')
                artifact.with_suffix('.ir.sig').write_text('IR signatures')
                self.external['Dep'] = source, artifact
                self.imports.update({'Aglib': ['Aglib.One'], 'Aglib.One': ['Dep']})
                calls = []
                with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)):
                    kernel.replay(root, directory, batch_size=4)
                    if changed == 'source':
                        source.write_text('dirty dependency')
                    elif changed in {'ir', 'ir.sig'}:
                        artifact.with_suffix('.' + changed).write_text('changed IR artifact')
                    elif changed == 'remove-private':
                        Path(str(artifact) + '.private').unlink()
                    else:
                        Path(str(artifact) + changed).write_text('changed dependency artifact')
                    kernel.replay(root, directory, batch_size=4)
                    self.assertEqual(calls[-1], ['Aglib', 'Aglib.One'])

    def test_checker_compiler_and_effective_config_invalidate_all(self):
        for changed in ['lib/lean/LeanChecker.olean', 'src/lean/LeanChecker.lean',
                        'bin/lean', 'lib/libleanshared.dylib', 'config']:
            with self.subTest(changed=changed), tempfile.TemporaryDirectory() as temporary:
                root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
                calls = []
                with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)):
                    kernel.replay(root, directory, batch_size=4)
                    if changed == 'config':
                        (root / 'lakefile.toml').write_text('name = "Fixture"\nleanOptions = {autoImplicit = false}\n')
                    else:
                        (prefix / changed).write_text('changed executable/checker')
                    kernel.replay(root, directory, batch_size=4)
                    self.assertEqual(len(calls), 2)
                    self.assertEqual(len(calls[-1]), 3)

    def test_config_formatting_preserves_reuse_but_records_new_full_basis(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
            calls = []
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)):
                kernel.replay(root, directory, batch_size=4)
                original = self.record(directory, 'Aglib').read_bytes()
                (root / 'lakefile.toml').write_text('# cosmetic\nname="Fixture"\n')
                kernel.replay(root, directory, batch_size=1)
                self.assertEqual(len(calls), 1)
                self.assertEqual(self.record(directory, 'Aglib').read_bytes(), original)
                self.assertIn('snapshots', json.loads((directory / 'coverage.json').read_text())['basis'])

    def test_enrollment_changes_do_not_reassign_positional_receipts(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
            calls = []
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)):
                kernel.replay(root, directory, batch_size=4)
                original = self.record(directory, 'Aglib.One').read_bytes()
                source = Path('Aglib/Added.lean'); sources.add(source)
                (root / source).write_text('module\n')
                (root / '.lake/build/lib/lean' / source.with_suffix('.olean')).write_text('added artifact')
                kernel.replay(root, directory, batch_size=4)
                self.assertEqual(calls[-1], ['Aglib.Added'])
                self.assertEqual(self.record(directory, 'Aglib.One').read_bytes(), original)
                summary = json.loads((directory / 'coverage.json').read_text())
                self.assertEqual((summary['expected_modules'], summary['covered_modules']), (4, 4))
                sources.remove(source); (root / source).unlink()
                (root / '.lake/build/lib/lean' / source.with_suffix('.olean')).unlink()
                kernel.replay(root, directory, batch_size=4)
                self.assertEqual(len(calls), 2)
                summary = json.loads((directory / 'coverage.json').read_text())
                self.assertEqual((summary['expected_modules'], summary['covered_modules']), (3, 3))
                self.assertNotIn('Aglib.Added', summary['module_records'])

    def test_coherent_relocation_reuses_original_records_and_provenance(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = root / '.lake/verification/kernel'
            calls = []
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)):
                kernel.replay(root, directory, batch_size=4)
                original = self.record(directory, 'Aglib.One').read_bytes()
                relocated = Path(temporary) / 'moved'
                shutil.copytree(root, relocated)
                moved_receipts = relocated / '.lake/verification/kernel'
                kernel.replay(relocated, moved_receipts, batch_size=4)
                self.assertEqual(len(calls), 1)
                self.assertEqual(self.record(moved_receipts, 'Aglib.One').read_bytes(), original)
                old_basis = json.loads((moved_receipts / 'basis.json').read_text())
                self.assertEqual(old_basis['root'], str(root.resolve()))

    def test_missing_or_corrupt_original_receipt_log_resource_and_basis_fail_closed(self):
        for changed in ['receipt', 'log', 'resource', 'basis', 'missing-basis', 'missing-log']:
            with self.subTest(changed=changed), tempfile.TemporaryDirectory() as temporary:
                root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
                calls = []
                with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)):
                    kernel.replay(root, directory, batch_size=4)
                    receipt = self.record(directory, 'Aglib')
                    record = json.loads(receipt.read_text())
                    target = receipt if changed == 'receipt' else directory / record[changed.removeprefix('missing-')]
                    if changed == 'receipt' or changed.startswith('missing-'):
                        target.unlink()
                    else:
                        target.write_text('{}' if changed == 'basis' else 'corrupted evidence')
                    with self.assertRaises((RuntimeError, OSError, KeyError)):
                        kernel.replay(root, directory, batch_size=4)
                    self.assertEqual(len(calls), 1)

    def test_changed_then_restored_source_still_rejects_midrun_drift(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
            base = self.guarded([])
            def mutate(command, **kwargs):
                code = base(command, **kwargs)
                path = root / 'Aglib/One.lean'; old = path.read_bytes(); info = path.stat()
                path.write_text('temporary mutation'); path.write_bytes(old)
                os.utime(path, ns=(info.st_atime_ns, info.st_mtime_ns))
                return code
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=mutate):
                with self.assertRaisesRegex(RuntimeError, 'basis changed during'):
                    kernel.replay(root, directory, batch_size=4)
            self.assertFalse(list(directory.glob('module-*.json')))

    def test_no_full_digest_per_batch_and_final_capture_is_required(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
            calls = []
            original = kernel.closure_basis
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)), \
                    patch.object(kernel, 'closure_basis', wraps=original) as capture:
                kernel.replay(root, directory, batch_size=1)
                self.assertEqual(len(calls), 3)
                self.assertEqual(capture.call_count, 2)

    def test_unknown_source_metadata_never_reuses_a_module(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary); directory = Path(temporary) / 'receipts'
            artifact = root / '.lake/build/lib/lean/Unknown.olean'; artifact.write_text('compiled only')
            self.external['Unknown'] = None, artifact
            self.imports['Aglib.One'] = ['Unknown']
            calls = []
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)):
                kernel.replay(root, directory, batch_size=4)
                original = self.record(directory, 'Aglib.One').read_bytes()
                kernel.replay(root, directory, batch_size=4)
                self.assertEqual(calls[-1], ['Aglib.One'])
                self.assertNotEqual(self.record(directory, 'Aglib.One').read_bytes(), original)

    def test_compiled_import_metadata_fails_closed_on_incomplete_graph(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            def emit(command, **kwargs):
                kwargs['stdout'].write('AGLIB_KERNEL_IMPORTS ' + json.dumps({
                    'module': 'Aglib', 'artifacts': ['Aglib.olean'], 'source': 'Aglib.lean',
                    'imports': ['Missing']}) + '\n')
                kernel.write_json(kwargs['receipt'], {'exit_code': 0, 'guard_failure': None,
                                                      'owned_group_gone': True})
                return 0
            with patch.object(kernel, 'run', side_effect=emit):
                with self.assertRaisesRegex(RuntimeError, 'Missing compiled import metadata roots'):
                    kernel.import_graph(directory, directory, '/mock/lean', {}, directory, ['Aglib'])

    def test_client_stale_artifact_rejected_before_replay(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); (root / 'Consumer.lean').write_text('module\n')
            library = root / '.lake/build/lib/lean'; (library / 'Consumer').mkdir(parents=True)
            (library / 'Consumer.olean').write_bytes(b'current')
            (library / 'Consumer/Deleted.olean').write_bytes(b'stale')
            with self.assertRaisesRegex(RuntimeError, 'inventory'):
                kernel.proof_basis(root, root, client=True)

    def test_selected_replay_ignores_unrelated_missing_artifact(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary)
            (root / '.lake/build/lib/lean/AglibTest.olean').unlink()
            calls = []
            with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=self.guarded(calls)):
                kernel.replay(root, Path(temporary) / 'receipts', selected=['Aglib.One'], batch_size=1)
            self.assertEqual(calls, [['Aglib.One']])
            basis = json.loads((Path(temporary) / 'receipts/basis.json').read_text())
            self.assertEqual(basis['modules'], ['Aglib.One'])
            self.assertEqual(set(basis['source_hashes']), {'Aglib/One.lean'})
            summary = json.loads((Path(temporary) / 'receipts/probe.json').read_text())
            self.assertEqual(summary['status'], 'probe passed')
            self.assertEqual(summary['expected_modules'], 3)
            self.assertEqual(summary['covered_modules'], 1)

    def test_selected_replay_requires_imported_artifact_and_checks_its_drift(self):
        for mode in ['missing', 'changed']:
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                root, prefix, sources = self.fixture(temporary)
                self.imports['Aglib.One'] = ['AglibTest']
                artifact = root / '.lake/build/lib/lean/AglibTest.olean'
                if mode == 'missing':
                    artifact.unlink()
                base = self.guarded([])
                def mutate(command, **kwargs):
                    result = base(command, **kwargs)
                    artifact.write_bytes(b'changed imported artifact')
                    return result
                with self.patched(prefix, sources), patch.object(kernel, 'run', side_effect=mutate):
                    with self.assertRaises((RuntimeError, OSError, IndexError)):
                        kernel.replay(root, Path(temporary) / 'receipts', selected=['Aglib.One'], batch_size=1)

    def test_reviewed_legacy_adoption_preserves_raw_records_and_profile(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, prefix, sources = self.fixture(temporary)
            legacy, directory = Path(temporary) / 'old', Path(temporary) / 'new'
            legacy.mkdir(); directory.mkdir()
            with self.patched(prefix, sources):
                basis = kernel.proof_basis(root, prefix)
                profile = kernel.limits()
                raw = {key: basis[key] for key in ['root', 'modules', 'source_hashes', 'artifact_hashes',
                      'config_hashes', 'installed_LeanChecker_sha256', 'installed_LeanChecker_source_sha256']}
                raw.update(driver_sha256=kernel.LEGACY_DRIVER_SHA256, limits=profile)
                kernel.write_json(legacy / 'basis.json', raw)
                full = Path(temporary) / 'full.json'; kernel.write_json(full, {'root': str(root), 'source_hashes': basis['source_hashes']})
                runner = Path(temporary) / 'runner.py'; runner.write_text('fake audited fixture')
                for index, name in enumerate(basis['modules']):
                    log = legacy / f'module-{index:04}.log'; log.write_text(f'AGLIB_KERNEL_CHECKED {name} 0\n')
                    kernel.write_json(legacy / f'module-{index:04}.json', {'module': name,
                        'status': 'passed', 'new_constants': 0, 'log': str(log)})
                    kernel.write_json(legacy / f'resource-{index:04}.json', {'limits': profile,
                        'exit_code': 0, 'guard_failure': None, 'owned_group_gone': True})
                original = (legacy / 'basis.json').read_bytes()
                with patch.object(kernel, 'LEGACY_RUNNER_SHA256', kernel.digest(runner)):
                    kernel.adopt_legacy(directory, legacy, full, runner, basis)
                self.assertEqual((legacy / 'basis.json').read_bytes(), original)
                self.assertEqual((directory / 'legacy-raw/basis.json').read_bytes(), original)
                for path in directory.glob('module-*.json'):
                    record = json.loads(path.read_text())
                    self.assertEqual(record['execution_profile']['limits']['lean_threads'], 1)
                    kernel.validate_record(record, directory, kernel.json_hash(basis))
                raw['driver_sha256'] = 'unreviewed'; kernel.write_json(legacy / 'basis.json', raw)
                with patch.object(kernel, 'LEGACY_RUNNER_SHA256', kernel.digest(runner)):
                    with self.assertRaisesRegex(RuntimeError, 'Unrecognized legacy embedded'):
                        kernel.adopt_legacy(directory, legacy, full, runner, basis)


if __name__ == '__main__':
    unittest.main()
