"""Bounded orchestration fixtures for local/CI sharing; no Lean is launched."""
from contextlib import nullcontext
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from lean_ci import build
from lean_ci.engine import Application, implementation_identity
from lean_ci.mappings import export_mappings, read_mapping
from lean_ci.recipe import native_recipe
from lean_ci.runtime import NativeRuntime
from lean_ci.state import (InputDrift, TemporalInputs, check_binding, file_hash,
                           read_json, write_json)
import test_engine as fixtures


class LocalPolicy:
    def __init__(self):
        self.callback = None
        self.native = False

    def local_inputs(self, root, requested_base=None, targets=()):
        return ['policy.py', 'Quartz/Base.lean', 'absent-policy.json',
                {'path': '.', 'exclude': ['.git', '.lake']}, 'Quartz']

    def select_scope(self, root, requested_base=None, targets=(), source_basis=None):
        if self.callback:
            self.callback(root)
        return {'scope': {'native': self.native}, 'requested': list(targets)}

    def tasks(self, root, plan, phase, directory):
        preflight = {'id': 'style', 'kind': 'check', 'check_kind': 'style', 'modules': [],
                     'command': ['python3', '-c', '# style'], 'cwd': str(root),
                     'input_boundary': {'kind': 'source-style', 'version': 1}, 'native': False}
        if not self.native:
            return [preflight]
        return native_recipe(root, directory, source_checks=[preflight], root_workspace={
            'id': 'root', 'modules': ['Quartz.Base'], 'selection': 'module',
            'checks': [{'id': 'builtin', 'kind': 'check', 'check_kind': 'builtin',
                        'command': ['python3', '-c', '# builtin'], 'modules': ['Quartz.Base']}]})

    def binding(self, root, task, toolchain, reflection=None, observations=None):
        value = check_binding(Path(task['cwd']), task['check_kind'], task['modules'], task['command'],
                              ['policy.py'], raw_paths=['Quartz/Base.lean'],
                              toolchain=toolchain, hash_file=observations.hash_file)
        value['reflective_imports'] = reflection.closure(task['modules']) if reflection else None
        return value


class SharedTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='lean-ci-shared-')
        self.addCleanup(temporary.cleanup)
        self.scratch = Path(temporary.name).resolve()
        self.root = self.scratch / 'repo'
        (self.root / 'Quartz').mkdir(parents=True)
        (self.root / 'Quartz/Base.lean').write_text('module\ndef x := 1\n')
        (self.root / 'policy.py').write_text('# policy\n')
        (self.root / '.gitignore').write_text('.lake/\n')
        for args in (['init', '-q'], ['config', 'user.name', 'Fixture'],
                     ['config', 'user.email', 'fixture@example.invalid'], ['add', '.'],
                     ['commit', '-qm', 'fixture']):
            subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True)
        self.policy = LocalPolicy()
        self.app = Application(self.root, self.policy)
        self.executor = fixtures.FixtureExecutor(self.root)

    def check(self, **kwargs):
        return self.app.check(self.scratch / 'state', progress=self.scratch / 'progress',
                              executor=self.executor, **kwargs)

    def test_dirty_source_only_check_needs_no_compiler_or_ci_plan_and_reuses(self):
        (self.root / 'Quartz/Base.lean').write_text('module\ndef x := 2\n')
        with patch.object(self.app.runtime, 'compiler_identity', side_effect=AssertionError('compiler')):
            first = self.check()
            second = self.check()
        self.assertEqual(first['source_basis']['kind'], 'working-tree')
        self.assertEqual(first['performed_checks'], ['style'])
        self.assertEqual(second['reused_checks'], ['style'])
        self.assertFalse((self.scratch / 'state/plan.json').exists())
        with self.assertRaisesRegex(ValueError, 'working-tree changes'):
            self.app._clean_head(first['source_basis']['head'])

    def test_selector_mutation_of_observed_policy_fails_before_any_command(self):
        self.policy.callback = lambda root: (root / 'policy.py').write_text('# changed\n')
        with self.assertRaises(InputDrift):
            self.check()
        self.assertEqual(self.executor.calls, [])

    def test_selector_new_enrolled_source_and_absent_policy_fail(self):
        for relative in ('Quartz/New.lean', 'absent-policy.json'):
            with self.subTest(relative=relative):
                self.policy.callback = lambda root, name=relative: (root / name).write_text('new\n')
                with self.assertRaises(InputDrift):
                    self.check()
                (self.root / relative).unlink()
        self.assertEqual(self.executor.calls, [])

    def test_source_check_mutation_is_rejected_before_recorded_success(self):
        self.executor.callback = lambda task: (self.root / 'Quartz/Base.lean').write_text('changed\n')
        with self.assertRaises(InputDrift):
            self.check()
        self.assertFalse((self.scratch / 'state/complete.json').exists())

    def test_local_partial_failure_retains_compatible_checks(self):
        (self.root / 'Init.lean').write_text('module\n')
        fixtures.native_fixture(self.root, 'Init')
        fixtures.native_fixture(self.root, 'Quartz.Base')
        self.policy.native = True
        self.executor.fail = 'builtin'
        with self.assertRaisesRegex(ValueError, 'fixture command failed'):
            self.check(toolchain=fixtures.TOOLCHAIN)
        self.assertFalse((self.scratch / 'state/complete.json').exists())
        self.executor.fail = None
        summary = self.check(toolchain=fixtures.TOOLCHAIN)
        self.assertEqual(summary['reused_checks'], ['style'])
        self.assertEqual(summary['performed_checks'], ['builtin'])

    def test_source_only_auto_state_has_no_plan(self):
        summary = self.app.check(executor=self.executor)
        directory = Path(summary['directory'])
        self.addCleanup(lambda: __import__('shutil').rmtree(directory))
        self.assertTrue((directory / 'local.json').is_file())
        self.assertFalse((directory / 'plan.json').exists())

    def test_source_only_outputs_does_not_require_native_mappings(self):
        outputs = self.scratch / 'outputs.jsonl'
        summary = self.check(outputs=outputs)
        self.assertEqual(summary['status'], 'complete')
        self.assertFalse(outputs.exists())

    def test_git_selection_mutation_is_rejected(self):
        def change_index(root):
            subprocess.run(['git', 'update-index', '--assume-unchanged', 'policy.py'],
                           cwd=root, check=True, capture_output=True)
        self.policy.callback = change_index
        with self.assertRaises(InputDrift):
            self.check()
        self.assertEqual(self.executor.calls, [])

    def test_changed_checker_invalidates_source_check_success(self):
        self.check()
        (self.root / 'policy.py').write_text('# repaired checker\n')
        summary = self.check()
        self.assertEqual(summary['performed_checks'], ['style'])
        self.assertEqual(self.executor.calls, ['style', 'style'])

    def test_directory_enrollment_ignores_only_explicit_setup_entries(self):
        observer = TemporalInputs()
        observer.observe_directory(self.root, ['.lake'])
        (self.root / '.lake').mkdir()
        observer.assert_stable()
        (self.root / 'Shadow.lean').write_text('module\n')
        with self.assertRaises(InputDrift):
            observer.assert_stable()

    def test_package_cwd_and_client_reflection_are_distinct(self):
        package = self.root / 'lean'
        client = self.root / 'client'
        package.mkdir(); client.mkdir()
        app = Application(self.root, self.policy, package_cwd=package)
        seen = []
        with patch('lean_ci.execution.ReflectionGraph', side_effect=lambda root,*args,**kwargs: seen.append(root) or root):
            one = app._reflection({'search_path': []}, fixtures.TOOLCHAIN, TemporalInputs(), package)
            two = app._reflection({'search_path': []}, fixtures.TOOLCHAIN, TemporalInputs(), client)
        self.assertEqual((one, two), (package, client))
        with self.assertRaisesRegex(ValueError, 'inside'):
            Application(self.root, self.policy, package_cwd=self.scratch)
        self.assertEqual(app.runtime.root, package)

    def test_setup_mutation_retains_absent_guard_and_gives_preparation_guidance(self):
        observer = TemporalInputs()
        observer.optional_hash(self.root / 'lakefile.lean')
        (self.root / '.lake').mkdir()
        with self.assertRaisesRegex(InputDrift, 'prepared before a local final check'):
            self.app._observe_inputs({'establishes_inputs': True}, observer)

    def test_recipe_one_graph_per_workspace_and_explicit_export_order(self):
        tasks = native_recipe(self.root, self.scratch / 'run',
            root_workspace={'id': 'root', 'modules': ['Quartz.Base', 'Quartz.Base']},
            clients=[{'id': 'client', 'cwd': '.', 'modules': ['Quartz.Base']}],
            exports=['root', 'client'])
        self.assertEqual([task['id'] for task in tasks], ['root/build', 'client/build'])
        self.assertEqual(tasks[0]['command'][3], '+Quartz.Base')
        self.assertEqual(tasks[0]['modules'], ['Quartz.Base'])
        self.assertEqual(tasks[0]['export_order'], 0)
        self.assertIn('recipe.py', implementation_identity())
        self.assertIn('execution.py', implementation_identity())

    def test_recipe_preserves_existing_mixed_graph_and_avoids_barrier_query(self):
        task = {'id': 'mixed', 'kind': 'graph-build', 'command': ['lake', '--rehash', 'build',
                'Quartz', '+Check', 'batteries/runLinter'], 'modules': ['Quartz.Base']}
        tasks = native_recipe(self.root, self.scratch / 'run', root_workspace={
            'id': 'root', 'build_task': task}, clients=[{'id': 'barrier', 'build': False,
            'checks': [{'id': 'barrier', 'kind': 'process', 'command': ['lake', '--no-build', 'build', 'Quartz']}]}])
        self.assertEqual(len(tasks), 2)
        self.assertEqual(tasks[0]['command'], task['command'])

    def mapping(self, name, rows):
        path = self.scratch / name
        path.write_text('"2026-03-17"\n' + ''.join(json.dumps(row) + '\n' for row in rows))
        return path

    def producer(self, path, cwd=None, order=0):
        task = {'id': path.name, 'cwd': str(cwd or self.root), 'mapping': str(path),
                'modules': ['Quartz.Base'], 'command': ['lake', '--no-build', 'build', 'Quartz'],
                'export_order': order}
        return task, {'receipt': fixtures.receipt(task), 'mapping_sha256': file_hash(path)}

    def test_mapping_export_merges_compatible_and_keeps_client_namespace(self):
        a = self.mapping('a.jsonl', [['0' * 16, {'o': 'a'}]])
        b = self.mapping('b.jsonl', [['1' * 16, {'o': 'b'}]])
        c = self.mapping('c.jsonl', [['0' * 16, {'o': 'client'}]])
        output = self.scratch / 'accepted.jsonl'
        groups = export_mappings([self.producer(c, self.root / 'client', 2),
            self.producer(a, order=0), self.producer(b, order=1)], output,
            fixtures.TOOLCHAIN, TemporalInputs())
        self.assertEqual(len(groups), 2)
        self.assertEqual(groups[0]['domain']['workspace'], str(self.root))
        self.assertEqual(len(read_mapping(output)[1]), 2)
        self.assertEqual(len(output.read_text().splitlines()), 3)
        self.assertEqual(len(read_mapping(groups[1]['path'])[1]), 1)

    def test_mapping_export_rejects_conflict_bad_header_and_receipt(self):
        a = self.mapping('a.jsonl', [['0' * 16, {'o': 'a'}]])
        b = self.mapping('b.jsonl', [['0' * 16, {'o': 'b'}]])
        with self.assertRaisesRegex(ValueError, 'Conflicting'):
            export_mappings([self.producer(a), self.producer(b)], self.scratch / 'out',
                            fixtures.TOOLCHAIN, TemporalInputs())
        a.write_text('"2099-01-01"\n')
        with self.assertRaisesRegex(ValueError, 'header'):
            read_mapping(a)
        task, result = self.producer(b)
        result['receipt']['exit_code'] = 1
        with self.assertRaisesRegex(ValueError, 'receipt'):
            export_mappings([(task, result)], self.scratch / 'out', fixtures.TOOLCHAIN, TemporalInputs())

    def test_mapping_group_side_path_cannot_enter_source_repository(self):
        a = self.mapping('a.jsonl', [['0' * 16, {'o': 'a'}]])
        b = self.mapping('b.jsonl', [['1' * 16, {'o': 'b'}]])
        output = self.scratch / 'accepted.jsonl'
        output.with_name(output.name + '.groups').symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'source repository'):
            export_mappings([self.producer(a), self.producer(b, self.root / 'client')], output,
                            fixtures.TOOLCHAIN, TemporalInputs(), repository_root=self.root)
        self.assertFalse((self.root / '0001.jsonl').exists())

    def test_native_build_cache_hit_propagates_mapping_and_semantic_targets(self):
        directory = self.scratch / 'run'; directory.mkdir()
        mapping = self.mapping('native.jsonl', [['0' * 16, {'o': 'a'}]])
        command = ['lake', '--rehash', 'build', '+Quartz.Base', '-o', str(mapping)]
        task = {'id': 'graph', 'kind': 'build', 'cwd': str(self.root), 'modules': ['Quartz.Base'],
                'build_selection': 'module', 'mapping': str(mapping), 'command': command}
        cached_task = dict(task, command=command[:2] + ['--no-build'] + command[2:])
        write_json(directory / 'cached-check.json', fixtures.receipt(cached_task))
        with patch.object(build, 'build', return_value=0) as selected:
            result = NativeRuntime(self.root).run(task, directory)
        self.assertEqual(result['mapping_sha256'], file_hash(mapping))
        self.assertEqual(selected.call_args.args[1], ['Quartz.Base'])
        self.assertEqual(selected.call_args.kwargs['selection'], 'module')
        self.assertEqual(selected.call_args.kwargs['outputs'], mapping)
        self.assertEqual(result['reused_build_targets'], ['Quartz.Base'])

    def test_native_performed_build_retains_mapping_and_validates_receipt(self):
        directory = self.scratch / 'run'; directory.mkdir()
        mapping = self.mapping('native.jsonl', [['0' * 16, {'o': 'a'}]])
        command = ['lake', '--rehash', 'build', '+Quartz.Base', '-o', str(mapping)]
        task = {'id': 'graph', 'kind': 'build', 'cwd': str(self.root), 'modules': ['Quartz.Base'],
                'build_selection': 'module', 'mapping': str(mapping), 'command': command}
        miss = fixtures.receipt(dict(task, command=command[:2] + ['--no-build'] + command[2:]))
        miss['exit_code'] = 3
        write_json(directory / 'cached-check.json', miss)
        (directory / 'cached-check.log').write_text('error: target is out-of-date and needs to be rebuilt\n')
        write_json(directory / 'graph-build.json', fixtures.receipt(task))
        with patch.object(build, 'build', return_value=0):
            result = NativeRuntime(self.root).run(task, directory)
        self.assertEqual(result['mapping_sha256'], file_hash(mapping))
        corrupted = fixtures.receipt(task)
        corrupted['command'] = ['false']
        write_json(directory / 'graph-build.json', corrupted)
        with patch.object(build, 'build', return_value=0), self.assertRaisesRegex(ValueError, 'receipt'):
            NativeRuntime(self.root).run(task, directory)

    def test_finalizer_exports_multiple_verified_mapping_tasks_without_build(self):
        (self.root / 'Init.lean').write_text('module\n')
        fixtures.native_fixture(self.root, 'Init')
        fixtures.native_fixture(self.root, 'Quartz.Base')
        subprocess.run(['git', 'add', '.'], cwd=self.root, check=True, capture_output=True)
        subprocess.run(['git', 'commit', '-qm', 'fixture imports'], cwd=self.root, check=True, capture_output=True)
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=self.root, text=True).strip()
        class Policy(fixtures.QuartzAdapter):
            def tasks(self, root, plan, phase, directory):
                tasks = super().tasks(root, plan, phase, directory)
                if phase == 'native':
                    for index in range(2):
                        tasks.append({'id': 'mapping-' + str(index), 'kind': 'process', 'cwd': str(root),
                            'command': ['lake', '--no-build', 'build', 'Quartz.Base', '-o', str(directory / f'{index}.jsonl')],
                            'mapping': str(directory / f'{index}.jsonl'), 'modules': ['Quartz.Base']})
                return tasks
        class Executor(fixtures.FixtureExecutor):
            def run(self, task, directory):
                result = super().run(task, directory)
                if task.get('mapping'):
                    Path(task['mapping']).write_text('"2026-03-17"\n' + json.dumps([task['id'][-1] * 16, {'o': task['id']}]) + '\n')
                    result['mapping_sha256'] = file_hash(task['mapping'])
                return result
        app = Application(self.root, Policy())
        executor = Executor(self.root)
        state = self.scratch / 'ci-state'
        app.plan('fixture/repo', 'main', head, state)
        app.run_phase(state, 'source', executor=executor)
        app.run_phase(state, 'native', executor=executor, toolchain=fixtures.TOOLCHAIN)
        count = len(executor.calls)
        summary = app.finalize(state, self.scratch / 'outputs.jsonl', toolchain=fixtures.TOOLCHAIN)
        self.assertEqual(len(executor.calls), count)
        self.assertEqual(len(summary['mapping_groups']), 1)
        self.assertEqual(len(read_mapping(self.scratch / 'outputs.jsonl')[1]), 2)

    def test_generated_program_argument_is_explicit_before_module_arguments(self):
        task = {'id': 'audit', 'kind': 'process', 'cwd': str(self.root),
                'command': ['lake', 'env', 'lean', '--run', str(self.scratch / 'Audit.lean'), 'Quartz.Base'],
                'generated_path': str(self.scratch / 'Audit.lean'), 'generated_argument_index': 4,
                'generated': 'module\n'}
        directory = self.scratch / 'run'
        def guarded(command, **kwargs):
            write_json(kwargs['receipt'], fixtures.receipt(task))
            return 0
        with patch('lean_ci.runtime.resources.limits', return_value={}), \
             patch('lean_ci.runtime.resources.run', side_effect=guarded):
            NativeRuntime(self.root).run(task, directory)
        self.assertEqual((self.scratch / 'Audit.lean').read_text(), 'module\n')
        self.assertFalse((self.root / 'Quartz.Base').exists())


if __name__ == '__main__':
    unittest.main()
