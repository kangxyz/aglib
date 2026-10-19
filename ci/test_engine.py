"""Package-only lifecycle tests with a second library; no Lean is launched.

Receipts/native artifacts below are synthetic orchestration fixtures. They do
not certify a compiler run, lint coverage, or a mathematical assertion.
"""
import contextlib
import io
import json
import os
import shutil
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from lean_ci.cli import main
from lean_ci.engine import Application, implementation_identity, implementation_sources
from lean_ci.runtime import NativeRuntime
from lean_ci.source import lean_imports, module_path
from lean_ci.state import check_binding, file_hash, read_json, write_json


TOOLCHAIN = {'lean': 'fixture-lean', 'lake': 'fixture-lake', 'installation': '/fixture/toolchain'}


def receipt(task):
    return {'state': 'completed', 'command': task['command'], 'cwd': task['cwd'],
            'exit_code': 0, 'guard_failure': None, 'owned_group_gone': True}


def native_fixture(root, name):
    relative = str(module_path(name).with_suffix(''))
    outputs = {'o': ['0' * 16 + suffix for suffix in ('.olean', '.olean.server', '.olean.private')],
               'i': '0' * 16 + '.ilean', 'r': '0' * 16 + '.ir',
               'rs': '0' * 16 + '.ir.sig', 'c': '0' * 16 + '.c', 'm': True}
    for suffix in ('.olean', '.olean.server', '.olean.private', '.ilean', '.ir', '.ir.sig', '.c'):
        directory = '.lake/build/ir' if suffix == '.c' else '.lake/build/lib/lean'
        path = root / directory / (relative + suffix)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(('fixture ' + name + suffix).encode())
    imports = lean_imports((root / module_path(name)).read_text())
    write_json(root / '.lake/build/lib/lean' / (relative + '.ilean'),
               {'version': 5, 'module': name,
                'directImports': [[item, False, False, False] for item in imports]})
    write_json(root / '.lake/build/lib/lean' / (relative + '.trace'),
               {'schemaVersion': '2025-09-10', 'synthetic': True, 'outputs': outputs,
                'depHash': '0123456789abcdef'})


class QuartzAdapter:
    """An independent fixture policy, containing no dependency on scripts/."""
    def __init__(self, native=True):
        self.native = native
        self.reflective = True
        self.optional_observed = False

    def plan(self, root, repository, default_branch, head, requested_base=None, api=None):
        return {'baseline': {'fixture': True}, 'scope': {'native': self.native}}

    def required_phases(self, root, plan):
        return ['source', 'native'] if self.native else ['source']

    def validate_plan(self, root, plan):
        if plan['scope'] != {'native': self.native}:
            raise ValueError('Fixture policy scope differs')

    def tasks(self, root, plan, phase, directory):
        def task(name, kind='process', **extra):
            return {'id': name, 'kind': kind, 'command': ['python3', '-c', '# ' + name],
                    'cwd': str(root), **extra}
        if phase == 'source':
            return [task('layout')]
        return [task('setup', establishes_inputs=True),
                task('graph', kind='graph-build', modules=['Quartz.Base']),
                task('search', kind='environment', environment_output=str(directory / 'search.txt')),
                task('builtin', kind='check', check_kind='builtin', modules=['Quartz.Base']),
                task('declarations', kind='check', check_kind='declaration', modules=['Quartz.Base'])]

    def binding(self, root, task, toolchain, reflection=None, observations=None):
        value = check_binding(root, task['check_kind'], task['modules'], task['command'],
                              ['policy.py', 'optional-policy.json'], raw_paths=['Quartz/Base.lean'],
                              toolchain=toolchain, hash_file=observations.hash_file)
        value['reflective_imports'] = (reflection.closure(task['modules'])
                                      if reflection and self.reflective else None)
        return value

    def observe_inputs(self, root, observations):
        observations.optional_hash(root / 'optional-policy.json')
        self.optional_observed = True

    def summary(self, root, plan, records):
        return {'coverage': 'synthetic fixture coverage'}


class FixtureExecutor:
    def __init__(self, root, fail=None, missing=None, wrong=None, callback=None):
        self.root, self.fail, self.missing, self.wrong = root, fail, missing, wrong
        self.callback = callback
        self.calls = []

    def run(self, task, directory):
        self.calls.append(task['id'])
        directory.mkdir(parents=True, exist_ok=True)
        if task['id'] == self.fail:
            raise ValueError('Actual fixture command failed')
        if task['id'] == self.missing:
            return {}
        if self.callback:
            self.callback(task)
        result = {'receipt': receipt(task)}
        if task['id'] == self.wrong:
            result['receipt']['command'] = ['false']
        if task['kind'] == 'environment':
            path = Path(task['environment_output'])
            paths = [str(self.root / '.lake/build/lib/lean')]
            path.write_text(os.pathsep.join(paths) + '\n')
            result.update(search_path=paths, output_sha256=file_hash(path))
        return result


class EngineTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='lean-ci-quartz-')
        self.addCleanup(self.temporary.cleanup)
        self.scratch = Path(self.temporary.name).resolve()
        self.root = self.scratch / 'QuartzLibrary'
        self.root.mkdir()
        for name, content in {'.gitignore': '.lake/\n', 'Quartz/Base.lean': 'module\ndef x := 1\n',
                              'Init.lean': 'module\n', 'policy.py': '# fixture policy\n'}.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        native_fixture(self.root, 'Init')
        native_fixture(self.root, 'Quartz.Base')
        self.git('init', '-q')
        self.git('config', 'user.name', 'Fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.commit()
        self.state = self.scratch / 'state'
        self.adapter = QuartzAdapter()
        self.application = Application(self.root, self.adapter)

    def git(self, *arguments):
        return subprocess.check_output(['git', *arguments], cwd=self.root, text=True).strip()

    def commit(self):
        self.git('add', '.')
        self.git('commit', '-qm', 'fixture source')
        self.head = self.git('rev-parse', 'HEAD')

    def plan(self):
        return self.application.plan('fixture/quartz', 'main', self.head, self.state)

    def source(self, executor=None):
        return self.application.run_phase(self.state, 'source', executor=executor or FixtureExecutor(self.root))

    def native(self, executor=None, toolchain=TOOLCHAIN):
        return self.application.run_phase(self.state, 'native', executor=executor or FixtureExecutor(self.root),
                                          toolchain=toolchain)

    def test_source_only_and_native_skips_never_publish_complete(self):
        self.plan()
        with self.assertRaises(OSError):
            self.native()
        self.source()
        with self.assertRaises(OSError):
            self.application.finalize(self.state, toolchain=TOOLCHAIN)
        self.assertFalse((self.state / 'complete.json').exists())
        write_json(self.state / 'native.json', {'status': 'skipped'})
        with self.assertRaisesRegex(ValueError, 'Missing/incomplete'):
            self.application.finalize(self.state, toolchain=TOOLCHAIN)

    def test_second_library_partial_success_is_reused_and_failed_check_runs(self):
        self.plan(); self.source()
        first = FixtureExecutor(self.root, fail='declarations')
        with self.assertRaisesRegex(ValueError, 'fixture command failed'):
            self.native(first)
        self.assertEqual(len(list((self.state / 'check-progress').glob('*.json'))), 1)
        retry = FixtureExecutor(self.root)
        result = self.native(retry)
        checks = {item['id']: item['result']['mode'] for item in result['tasks'] if 'mode' in item['result']}
        self.assertEqual(checks, {'builtin': 'reused', 'declarations': 'performed'})
        self.assertNotIn('builtin', retry.calls)
        self.assertIn('declarations', retry.calls)
        self.assertTrue(self.adapter.optional_observed)
        summary = self.application.finalize(self.state, toolchain=TOOLCHAIN)
        self.assertEqual(summary['status'], 'complete')
        self.assertEqual(summary['reused_checks'], ['builtin'])

    def implementation_copy(self, directory):
        directory.mkdir()
        result = {}
        for name, source in implementation_sources().items():
            result[name] = directory / name
            shutil.copyfile(source, result[name])
        return result

    def test_actual_implementation_identity_is_location_independent_and_reserved(self):
        first = self.implementation_copy(self.scratch / 'installed-first')
        second = self.implementation_copy(self.scratch / 'installed-second')
        with patch('lean_ci.engine.implementation_sources', return_value=first):
            original = implementation_identity()
        with patch('lean_ci.engine.implementation_sources', return_value=second):
            self.assertEqual(implementation_identity(), original)
            plan = self.plan()
            self.assertEqual(plan['implementation'], original)
            self.source(); self.native()
            summary = self.application.finalize(self.state, toolchain=TOOLCHAIN)
            self.assertEqual(summary['implementation'], original)
            self.adapter.summary = lambda *args: {'implementation': {}}
            with self.assertRaisesRegex(ValueError, 'override core'):
                self.application.finalize(self.state, toolchain=TOOLCHAIN)

    def test_actual_implementation_drift_blocks_plan_consumption(self):
        copied = self.implementation_copy(self.scratch / 'installed')
        with patch('lean_ci.engine.implementation_sources', return_value=copied):
            self.plan()
            copied['runtime.py'].write_bytes(b'changed installed runtime')
            with self.assertRaisesRegex(ValueError, 'implementation bytes'):
                self.source()
            self.assertFalse((self.state / 'complete.json').exists())

    def test_actual_implementation_restoration_blocks_check_save(self):
        copied = self.implementation_copy(self.scratch / 'installed')
        with patch('lean_ci.engine.implementation_sources', return_value=copied):
            self.plan(); self.source()
            def mutate(task):
                if task['id'] == 'builtin':
                    path = copied['runtime.py']
                    original = path.read_bytes()
                    path.write_bytes(b'transient implementation')
                    path.write_bytes(original)
            with self.assertRaisesRegex(ValueError, 'changed'):
                self.native(FixtureExecutor(self.root, callback=mutate))
            self.assertFalse(list((self.state / 'check-progress').glob('*.json')))

    def test_changed_implementation_invalidates_individual_check_reuse(self):
        copied = self.implementation_copy(self.scratch / 'installed')
        progress = self.scratch / 'shared-progress'
        with patch('lean_ci.engine.implementation_sources', return_value=copied):
            self.plan(); self.source()
            self.application.run_phase(self.state, 'native', progress=progress,
                                       executor=FixtureExecutor(self.root), toolchain=TOOLCHAIN)
            copied['runtime.py'].write_bytes(copied['runtime.py'].read_bytes() + b'\n# changed implementation\n')
            new_state = self.scratch / 'new-implementation-state'
            self.application.plan('fixture/quartz', 'main', self.head, new_state)
            self.application.run_phase(new_state, 'source', executor=FixtureExecutor(self.root))
            result = self.application.run_phase(new_state, 'native', progress=progress,
                                                executor=FixtureExecutor(self.root), toolchain=TOOLCHAIN)
            self.assertEqual([item['result']['mode'] for item in result['tasks'] if 'mode' in item['result']],
                             ['performed', 'performed'])

    def test_same_repository_relocation_reuses_logically_identical_checks(self):
        self.plan(); self.source(); self.native()
        moved = self.scratch / 'relocated-quartz'
        shutil.copytree(self.root, moved)
        application = Application(moved, QuartzAdapter())
        state = self.scratch / 'relocated-state'
        application.plan('fixture/quartz', 'main', self.head, state)
        application.run_phase(state, 'source', executor=FixtureExecutor(moved))
        executor = FixtureExecutor(moved)
        relocated_toolchain = dict(TOOLCHAIN, installation='/fixture/relocated-installation')
        result = application.run_phase(state, 'native', progress=self.state / 'check-progress',
                                       executor=executor, toolchain=relocated_toolchain)
        checks = [item for item in result['tasks'] if 'mode' in item['result']]
        self.assertEqual([item['result']['mode'] for item in checks], ['reused', 'reused'])
        self.assertNotIn('builtin', executor.calls)
        self.assertEqual(checks[0]['result']['success']['receipt']['cwd'], str(self.root))
        application.finalize(state, toolchain=relocated_toolchain)

    def test_changed_logical_working_directory_does_not_reuse(self):
        (self.root / 'client-a').mkdir()
        (self.root / 'client-b').mkdir()
        # Empty ignored directories are separate execution contexts, even when
        # this synthetic fixture's selected input bytes happen to be identical.
        selected = ['client-a']
        original_tasks = self.adapter.tasks
        def tasks(root, plan, phase, directory):
            result = original_tasks(root, plan, phase, directory)
            for task in result:
                if task['kind'] == 'check':
                    task['cwd'] = str(root / selected[0])
            return result
        self.adapter.tasks = tasks
        self.plan(); self.source(); self.native()
        selected[0] = 'client-b'
        executor = FixtureExecutor(self.root)
        result = self.native(executor)
        self.assertEqual([item['result']['mode'] for item in result['tasks'] if 'mode' in item['result']],
                         ['performed', 'performed'])

    def test_full_current_binding_mismatch_reruns_checks(self):
        self.plan(); self.source(); self.native()
        artifact = self.root / '.lake/build/lib/lean/Quartz/Base.olean.private'
        artifact.write_bytes(b'changed cached output')
        retry = FixtureExecutor(self.root)
        result = self.native(retry)
        self.assertEqual([item['result']['mode'] for item in result['tasks'] if 'mode' in item['result']],
                         ['performed', 'performed'])
        self.assertIn('builtin', retry.calls)
        self.assertIn('declarations', retry.calls)

    def test_unsupported_metadata_never_reuses_individual_checks(self):
        self.adapter.reflective = False
        self.plan(); self.source(); self.native()
        second = FixtureExecutor(self.root)
        result = self.native(second)
        self.assertEqual([item['result']['mode'] for item in result['tasks'] if 'mode' in item['result']],
                         ['performed', 'performed'])

    def test_wrong_commands_and_missing_receipts_fail_before_success_save(self):
        self.plan(); self.source()
        for executor in (FixtureExecutor(self.root, missing='builtin'),
                         FixtureExecutor(self.root, wrong='builtin'),
                         FixtureExecutor(self.root, missing='graph')):
            with self.subTest(executor=executor):
                with self.assertRaisesRegex(ValueError, 'receipt'):
                    self.native(executor)
                self.assertFalse(list((self.state / 'check-progress').glob('*.json')))

    def test_finalization_reconstructs_task_set(self):
        self.plan(); self.source(); self.native()
        record = read_json(self.state / 'native.json')
        record['tasks'].pop()
        write_json(self.state / 'native.json', record)
        with self.assertRaisesRegex(ValueError, 'coverage is incomplete'):
            self.application.finalize(self.state, toolchain=TOOLCHAIN)
        self.assertFalse((self.state / 'complete.json').exists())

    def test_dirty_source_and_restored_source_block_completion(self):
        self.plan()
        def mutate(task):
            target = self.root / 'policy.py'
            content = target.read_bytes()
            target.write_bytes(b'transient')
            target.write_bytes(content)
        with self.assertRaisesRegex(ValueError, 'changed'):
            self.source(FixtureExecutor(self.root, callback=mutate))
        self.assertNotEqual(read_json(self.state / 'source.json')['status'], 'completed')

    def test_optional_input_appearance_and_removal_blocks_check_save(self):
        self.plan(); self.source()
        def mutate(task):
            if task['id'] == 'builtin':
                optional = self.root / 'optional-policy.json'
                optional.write_text('{}')
                optional.unlink()
        with self.assertRaisesRegex(ValueError, 'resolution changed'):
            self.native(FixtureExecutor(self.root, callback=mutate))
        self.assertFalse(list((self.state / 'check-progress').glob('*.json')))

    def test_compiler_restoration_is_observed_before_cache_save_even_without_reflection(self):
        self.adapter.reflective = False
        self.plan(); self.source()
        prefix = self.scratch / 'actual-runtime'
        (prefix / 'bin').mkdir(parents=True)
        (prefix / 'lib/lean').mkdir(parents=True)
        for relative in ('bin/lean', 'bin/lake', 'lib/lean/libleanshared.so'):
            (prefix / relative).write_bytes(b'original runtime')
        shared = prefix / 'lib/lean/libleanshared.so'
        original = subprocess.check_output
        def locate(command, *arguments, **keywords):
            if command[:2] == ['elan', 'which']:
                return str(prefix / 'bin' / command[-1]) + '\n'
            return original(command, *arguments, **keywords)
        def mutate(task):
            if task['id'] == 'builtin':
                shared.write_bytes(b'different runtime')
                shared.write_bytes(b'original runtime')
        with patch('lean_ci.runtime.subprocess.check_output', side_effect=locate):
            with self.assertRaisesRegex(ValueError, 'changed'):
                self.native(FixtureExecutor(self.root, callback=mutate), toolchain=None)
        self.assertFalse(list((self.state / 'check-progress').glob('*.json')))

    def test_source_only_policy_requires_source_receipt(self):
        self.adapter.native = False
        self.plan()
        with self.assertRaises(OSError):
            self.application.finalize(self.state)
        self.source()
        self.assertEqual(self.application.finalize(self.state)['performed_phases'], ['source'])
        with self.assertRaisesRegex(ValueError, 'not required'):
            self.native()

    def test_summary_cannot_override_core_success(self):
        self.adapter.native = False
        self.plan(); self.source()
        self.adapter.summary = lambda *args: {'status': 'complete'}
        with self.assertRaisesRegex(ValueError, 'override core'):
            self.application.finalize(self.state)
        self.assertFalse((self.state / 'complete.json').exists())

    def test_cli_accepts_supplied_application_without_adapter_argument(self):
        self.adapter.native = False
        with contextlib.redirect_stdout(io.StringIO()):
            code = main(['plan', '--state', str(self.state), '--repository', 'fixture/quartz',
                         '--head', self.head], application=self.application)
        self.assertEqual(code, 0)
        self.assertEqual(read_json(self.state / 'plan.json')['required_phases'], ['source'])


if __name__ == '__main__':
    unittest.main()
