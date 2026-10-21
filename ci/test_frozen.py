"""Gitless frozen-source admission and shared runner fixtures; no Lean is run."""
import json
import os
from pathlib import Path
import tempfile
import sys
from types import ModuleType
import unittest
from unittest.mock import patch

from lean_ci.cli import main as cli_main
from lean_ci.engine import implementation_identity
from lean_ci.frozen import execute
from lean_ci.state import digest, file_hash
import test_engine as fixtures


POLICY = '''from pathlib import Path
from lean_ci.engine import Application
from lean_ci.runtime import NativeRuntime
from lean_ci.recipe import native_recipe
from lean_ci.state import check_binding
from helper import BOUNDARY
class Policy:
    def plan(self,*a,**k): raise AssertionError('CI plan forbidden')
    def local_inputs(self,*a,**k): raise AssertionError('local inventory forbidden')
    def select_scope(self,*a,**k): raise AssertionError('Git selection forbidden')
    def validate_local(self,*a,**k): raise AssertionError('local validation forbidden')
    def tasks(self,root,plan,phase,directory):
        assert phase == 'native'
        return native_recipe(root,directory,phase='native',root_workspace={
            'id':'root','modules':['Quartz.Base'], 'checks':[
            {'id':'style','kind':'check','check_kind':'style','modules':[],
             'command':['python3','-c','# frozen check'],'input_boundary':BOUNDARY}]})
    def binding(self,root,task,toolchain,reflection=None,observations=None):
        result=check_binding(root,'style',[],task['command'],['ci_adapter.py','helper.py'],
                             raw_paths=['Quartz/Base.lean'],toolchain=toolchain,
                             hash_file=observations.hash_file)
        result['reflective_imports']=None
        return result

def create_application(root):
    return Application(root,Policy())
'''


class FrozenTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='lean-ci-frozen-fixture-')
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name).resolve()
        self.root = self.directory / 'lean'
        (self.root / 'Quartz').mkdir(parents=True)
        (self.root / 'Quartz/Base.lean').write_text('module\ndef x := 1\n')
        (self.root / 'ci_adapter.py').write_text(POLICY)
        (self.root / 'helper.py').write_text("BOUNDARY={'kind':'source-style','schema':1}\n")
        (self.root / 'lean-toolchain').write_text('fixture-pinned-toolchain\n')
        (self.root / 'lakefile.toml').write_text('name = "Quartz"\n')
        (self.root / 'lake-manifest.json').write_text('{}\n')
        self.request_path = self.root / 'native-request.json'
        self.request = {'schema': 1, 'adapter': 'ci_adapter.py',
            'policy_inputs': ['ci_adapter.py', 'helper.py'],
            'payload': {'scope': {'native': True, 'modules': ['Quartz.Base']}},
            'implementation': implementation_identity(),
            'coordinates': {'root': '.', 'package_cwd': '.', 'source_mapping': {}}}
        self.manifest_path = self.directory / 'SOURCE.json'
        self.write_source()
        self.executor = fixtures.FixtureExecutor(self.root)

    def write_source(self, omit=()):
        self.request_path.write_text(json.dumps(self.request))
        files = {path.relative_to(self.root).as_posix(): file_hash(path)
                 for path in self.root.rglob('*') if path.is_file() and path.name not in omit}
        self.expected = digest(files)
        self.manifest = {'workspace': str(self.root), 'source_root': '/local/repo/lean',
                         'git_head': '0' * 40, 'files': files, 'content_sha256': self.expected}
        self.manifest_path.write_text(json.dumps(self.manifest))

    def run_request(self, **kwargs):
        def compiler(runtime, hash_file=None, *, cwd=None):
            return fixtures.TOOLCHAIN
        with patch('lean_ci.runtime.NativeRuntime.compiler_identity', compiler), \
             patch('lean_ci.runtime.NativeRuntime.run', side_effect=self.executor.run), \
             patch('lean_ci.engine.git', side_effect=AssertionError('Git forbidden')):
            return execute(self.request_path, source_manifest=self.manifest_path,
                           expected_source=kwargs.pop('expected_source', self.expected),
                           state=self.directory / 'state', **kwargs)

    def assert_before_policy(self, pattern, **kwargs):
        with patch('lean_ci.frozen.importlib.util.spec_from_file_location') as loader:
            with self.assertRaisesRegex((ValueError, FileNotFoundError), pattern):
                self.run_request(**kwargs)
            loader.assert_not_called()
        self.assertEqual(self.executor.calls, [])

    def test_gitless_source_runs_same_runner_and_reuses_exact_success(self):
        first = self.run_request()
        second = self.run_request()
        self.assertEqual(first['performed_checks'], ['style'])
        self.assertEqual(second['reused_checks'], ['style'])
        self.assertEqual(first['source_basis']['kind'], 'transport-snapshot')
        self.assertEqual(first['source_basis']['content_sha256'], self.expected)
        self.assertEqual(first['source_basis']['workspace'], str(self.root))
        self.assertEqual(first['outer_receipt_join']['expected_source'], self.expected)
        self.assertIn('separate', first['source_checks'])
        self.assertFalse((self.root / '.git').exists())
        self.assertFalse((self.directory / 'state/complete.json').exists())
        self.assertFalse((self.root / '__pycache__').exists())

    def test_missing_helper_or_request_is_rejected_before_policy(self):
        for omitted in ('helper.py', 'native-request.json', 'ci_adapter.py'):
            with self.subTest(omitted=omitted):
                self.write_source(omit=[omitted])
                self.assert_before_policy('SOURCE.files')

    def test_corrupted_helper_or_request_rejected_before_policy(self):
        for name in ('helper.py', 'native-request.json'):
            with self.subTest(name=name):
                self.write_source()
                path = self.root / name
                previous = path.read_bytes()
                path.write_bytes(previous + b' ')
                self.assert_before_policy('bytes differ')
                path.write_bytes(previous)

    def test_wrong_expected_source_and_implementation_rejected(self):
        self.assert_before_policy('wrong expected', expected_source='f' * 64)
        self.request['implementation']['frozen.py'] = 'f' * 64
        self.write_source()
        self.assert_before_policy('implementation')

    def test_invalid_source_digest_null_incomplete_or_owner_rejected(self):
        changes = ({'content_sha256': None}, {'sync_incomplete': True},
                   {'files': {}}, {'workspace': str(self.directory / 'other')})
        for change in changes:
            with self.subTest(change=change):
                self.write_source()
                self.manifest_path.write_text(json.dumps(dict(self.manifest, **change)))
                self.assert_before_policy('SOURCE|workspace|snapshot')

    def test_source_unsafe_paths_symlinks_and_duplicate_fields_rejected(self):
        self.manifest['files']['../escape.py'] = '0' * 64
        self.manifest['content_sha256'] = self.expected = digest(self.manifest['files'])
        self.manifest_path.write_text(json.dumps(self.manifest))
        self.assert_before_policy('Unsafe source path')
        self.write_source()
        helper = self.root / 'helper.py'
        helper.unlink()
        helper.symlink_to(self.root / 'ci_adapter.py')
        self.assert_before_policy('symlink')
        helper.unlink(); helper.write_text('# helper\n')
        self.write_source()
        self.manifest_path.write_text('{"files":{},"files":{}}')
        self.assert_before_policy('Duplicate')

    def test_all_admitted_bytes_not_only_selected_module_are_verified(self):
        extra = self.root / 'extra-policy.json'
        extra.write_text('{}')
        self.write_source()
        extra.write_text('{"changed":true}')
        self.assert_before_policy('bytes differ')

    def test_r5_explicit_flat_package_factory_receives_exact_mapping(self):
        adapter = self.root / 'ci_adapter.py'
        text = POLICY + '''
def create_native_application(root,package_cwd,source_mapping):
    assert root == package_cwd
    assert source_mapping == {'repository_package':'lean','transport_package':'.'}
    return Application(root,Policy(),package_cwd=package_cwd)
'''
        adapter.write_text(text)
        self.request['coordinates']['source_mapping'] = {'repository_package': 'lean', 'transport_package': '.'}
        self.write_source()
        summary = self.run_request()
        self.assertEqual(summary['coordinates']['package_cwd'], '.')
        self.assertEqual(summary['coordinates']['source_mapping']['repository_package'], 'lean')
        self.request['coordinates']['package_cwd'] = '../lean'
        self.write_source()
        self.executor.calls.clear()
        self.assert_before_policy('Unsafe source path')

    def test_remote_environment_defaults_and_unenrolled_profile_fail_closed(self):
        environment = {'LEAN_CI_SOURCE_MANIFEST': str(self.manifest_path),
                       'LEAN_CI_EXPECTED_SOURCE': self.expected}
        with patch.dict(os.environ, environment):
            with patch('lean_ci.runtime.NativeRuntime.compiler_identity', return_value=fixtures.TOOLCHAIN), \
                 patch('lean_ci.runtime.NativeRuntime.run', side_effect=self.executor.run):
                result = execute(self.request_path, state=self.directory / 'state')
            self.assertEqual(result['source_basis']['content_sha256'], self.expected)
        self.executor.calls.clear()
        with patch.dict(os.environ, {'R5_LEAN_REMOTE_PROFILE': '{}'}):
            with self.assertRaisesRegex(ValueError, 'profile'):
                self.run_request()
        self.assertEqual(self.executor.calls, [])

    def test_explicit_arguments_cannot_replace_parent_source_boundary(self):
        with patch.dict(os.environ, {'LEAN_CI_SOURCE_MANIFEST': str(self.manifest_path),
                                    'LEAN_CI_EXPECTED_SOURCE': self.expected}):
            self.assert_before_policy('conflicts with the owned worker', expected_source='f' * 64)
            with self.assertRaisesRegex(ValueError, 'conflicts with the owned worker'):
                execute(self.request_path, source_manifest=self.directory / 'other/SOURCE.json')

    def test_policy_source_drift_during_task_cannot_release_success(self):
        self.executor.callback = lambda task: (self.root / 'helper.py').write_text('# changed\n')
        with self.assertRaisesRegex(ValueError, 'changed'):
            self.run_request()
        self.assertFalse((self.directory / 'state/native-result.json').exists())

    def test_unadmitted_helper_import_is_rejected_before_helper_body(self):
        rogue = self.root / 'rogue.py'
        marker = self.directory / 'rogue-executed'
        rogue.write_text('from pathlib import Path\nPath(' + repr(str(marker)) + ').touch()\n')
        adapter = self.root / 'ci_adapter.py'
        adapter.write_text('import rogue\n' + POLICY)
        self.write_source(omit=['rogue.py'])
        with self.assertRaisesRegex(ValueError, 'Unadmitted'):
            self.run_request()
        self.assertFalse(marker.exists())

    def test_external_cached_helper_requires_immutable_admission(self):
        external = self.directory / 'external-helper.py'
        external.write_text("BOUNDARY={'kind':'immutable-tooling','schema':1}\n")
        cached = ModuleType('external_cached_helper')
        cached.__file__ = str(external)
        cached.BOUNDARY = {'kind': 'stale-cached-input'}
        adapter = self.root / 'ci_adapter.py'
        adapter.write_text('import external_cached_helper\n' + POLICY)
        self.write_source()
        with patch.dict(sys.modules, {'external_cached_helper': cached}):
            with self.assertRaisesRegex(ValueError, 'Unadmitted cached'):
                self.run_request()
        self.assertEqual(self.executor.calls, [])

    def test_missing_package_pin_is_rejected_before_policy(self):
        self.write_source(omit=['lean-toolchain'])
        self.assert_before_policy('pins/configuration')

    def test_source_only_task_cannot_enter_frozen_native_execution_or_verification(self):
        for stage in ('initial', 'verification'):
            with self.subTest(stage=stage):
                adapter = self.root / 'ci_adapter.py'
                adapter.write_text(POLICY + """
original_tasks = Policy.tasks
def guarded_tasks(self,root,plan,phase,directory):
    self.task_calls = getattr(self,'task_calls',0) + 1
    tasks = original_tasks(self,root,plan,phase,directory)
    if STAGE == 'initial' or self.task_calls > 1:
        tasks[0]['native'] = False
    return tasks
Policy.tasks = guarded_tasks
""".replace('STAGE', repr(stage)))
                self.write_source()
                self.executor.calls.clear()
                with self.assertRaisesRegex(ValueError, 'source-only tasks'):
                    self.run_request()
                if stage == 'initial':
                    self.assertEqual(self.executor.calls, [])
                self.assertFalse((self.directory / 'state/native-result.json').exists())

    def test_cli_execute_dispatches_without_git_adapter_loader(self):
        with patch('lean_ci.cli.load_application', side_effect=AssertionError('Git loader forbidden')), \
             patch('lean_ci.frozen.main', return_value=0) as runner:
            self.assertEqual(cli_main(['execute', 'native-request.json']), 0)
        runner.assert_called_once_with(['native-request.json'])


if __name__ == '__main__':
    unittest.main()
