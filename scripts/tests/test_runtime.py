"""Resource/build extraction checks using small Python children and fixtures."""
from contextlib import nullcontext, redirect_stderr
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

from lean_tools import build, resources
from lean_tools.runtime import CommandFailed, RuntimeFailure, NativeRuntime, compiler_identity
from lean_tools.state import TemporalInputs, read_json


class ResourceTests(unittest.TestCase):
    def test_two_instances_use_explicit_configuration_without_environment_leakage(self):
        environment = {'ALPHA_LEAN_MEMORY_MB': '128', 'ALPHA_RSS_LIMIT_MB': '512',
                       'BETA_LEAN_MEMORY_MB': '256', 'BETA_RSS_LIMIT_MB': '768'}
        alpha = NativeRuntime('.', resources.ResourceConfig(prefix='ALPHA'), environment)
        beta = NativeRuntime('.', resources.ResourceConfig(prefix='BETA'), environment)
        environment['ALPHA_LEAN_MEMORY_MB'] = '999'
        selected_alpha = resources.limits(alpha.environment, 8 * 1024**3, alpha.resource_config)
        selected_beta = resources.limits(beta.environment, 8 * 1024**3, beta.resource_config)
        self.assertEqual((selected_alpha['lean_memory_mb'], selected_alpha['rss_limit_mb']), (128, 512))
        self.assertEqual((selected_beta['lean_memory_mb'], selected_beta['rss_limit_mb']), (256, 768))
        self.assertEqual(build.build_threads({'LEAN_NUM_THREADS': '128'}), 1)
        with self.assertRaisesRegex(ValueError, 'Conflicting'):
            resources.limits({'LEAN_CI_LEAN_MEMORY_MB': '128', 'COMPAT_MEMORY': '256'},
                             8 * 1024**3, resources.ResourceConfig(memory_keys=('COMPAT_MEMORY',)))

    def managed(self, directory):
        prefix = Path(directory) / 'managed'
        (prefix / 'bin').mkdir(parents=True)
        lean = prefix / 'bin/lean'
        lean.write_text('#!/bin/false\n')
        lean.chmod(0o755)
        profile = {'schema_version': 1, 'jobs': 2, 'threads': 3,
                   'lean_memory_mib': 64, 'rss_limit_mib': 512, 'lean': str(lean)}
        return {'PARENT_PROFILE': json.dumps(profile), 'LEAN': str(lean), 'LEAN_SYSROOT': str(prefix),
                'LEAN_NUM_THREADS': '1', 'PATH': os.environ.get('PATH', '')}

    def test_managed_profile_is_explicit_scoped_and_reuses_approved_wrapper(self):
        with tempfile.TemporaryDirectory() as directory:
            environment = self.managed(directory)
            config = resources.ResourceConfig(profile_keys=('PARENT_PROFILE',))
            budget = resources.limits(environment, 8 * 1024**3, config)
            self.assertEqual((budget['lean_threads'], budget['max_active_lean']), (3, 2))
            self.assertIsNone(resources.remote_profile(environment))
            self.assertEqual(build.build_threads(environment, config), 3)
            with patch.object(build.subprocess, 'check_output') as locator:
                with build.capped_toolchain(Path(directory), environment=environment, config=config) as actual:
                    self.assertEqual(actual['LEAN'], environment['LEAN'])
                    self.assertEqual(actual['LEAN_NUM_THREADS'], '2')
                locator.assert_not_called()
            self.assertEqual(environment['LEAN_NUM_THREADS'], '1')
            environment['PARENT_PROFILE'] = '{'
            with self.assertRaisesRegex(ValueError, 'Invalid managed'):
                resources.remote_profile(environment, config)

    def test_monitor_permission_failure_prevents_child_launch(self):
        def unavailable(group):
            raise PermissionError('monitor unavailable')
        with patch.object(resources.subprocess, 'Popen') as launch:
            with self.assertRaises(PermissionError):
                resources.run([sys.executable, '-c', 'pass'], env={}, sampler=unavailable)
            launch.assert_not_called()

    def test_managed_memory_and_job_caps_do_not_reserve_their_product(self):
        with tempfile.TemporaryDirectory() as directory:
            environment = self.managed(directory)
            profile = json.loads(environment['PARENT_PROFILE'])
            profile.update(jobs=8, threads=4, lean_memory_mib=24576, rss_limit_mib=110592)
            environment['PARENT_PROFILE'] = json.dumps(profile)
            config = resources.ResourceConfig(profile_keys=('PARENT_PROFILE',))
            budget = resources.limits(environment, 128 * 1024**3, config)
            self.assertEqual((budget['lean_memory_mb'], budget['max_active_lean']), (24576, 8))
            profile['lean_memory_mib'] = profile['rss_limit_mib']
            environment['PARENT_PROFILE'] = json.dumps(profile)
            with self.assertRaisesRegex(ValueError, 'Invalid managed resource profile'):
                resources.limits(environment, 128 * 1024**3, config)

    def test_owned_group_rss_and_concurrency_cutoffs_are_preserved(self):
        for reason, members, expected in (
                ('rss', [{'pid': 42, 'rss_bytes': 513 * resources.MIB, 'executable': 'python'}], 137),
                ('fanout', [{'pid': 42 + i, 'rss_bytes': 1, 'executable': 'lean'} for i in range(2)], 125)):
            with self.subTest(reason=reason):
                calls = 0
                def sampler(group):
                    nonlocal calls
                    calls += 1
                    return members if calls == 2 else []
                child = Mock(pid=123456789)
                child.poll.return_value = None
                child.wait.return_value = -15
                budget = resources.limits({'LEAN_CI_LEAN_MEMORY_MB': '64', 'LEAN_CI_RSS_LIMIT_MB': '512'},
                                          8 * 1024**3)
                with patch.object(resources.subprocess, 'Popen', return_value=child), \
                     patch.object(resources, 'terminate_group') as terminate, \
                     patch.object(resources, 'metadata_process', return_value=False), \
                     redirect_stderr(io.StringIO()):
                    code = resources.run(['fixture-process'], env={}, sampler=sampler, budget=budget)
                self.assertEqual(code, expected)
                terminate.assert_called_once_with(child.pid, members)

    def test_small_child_exit_and_closed_group_receipt_are_actual(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'receipt.json'
            command = [sys.executable, '-c', 'import sys; sys.exit(7)']
            # The child is real; this deliberately injected empty sampler is not
            # evidence for platform monitoring permission or native execution.
            code = resources.run(command, env={}, receipt=path, sampler=lambda group: [])
            result = read_json(path)
            self.assertEqual(code, 7)
            self.assertEqual(result['exit_code'], 7)
            self.assertTrue(result['owned_group_gone'])
            self.assertEqual(result['command'], command)

    def test_frontend_cap_rewriting_rejects_shells_and_preserves_direct_arguments(self):
        environment = {'LEAN': '/owned overlay/bin/lean'}
        command = ['lake', 'env', 'lean', '--setup', 'setup with spaces.json', 'Main.lean']
        self.assertEqual(resources.capped_command(command, environment),
                         ['lake', 'env', environment['LEAN'], *command[3:]])
        for unsafe in (['sh', '-c', 'lean Main.lean'], ['lake', 'env', 'python3', 'driver.py']):
            with self.assertRaises(ValueError):
                resources.capped_command(unsafe, environment)

    def test_build_runs_one_native_graph_for_hits_misses_and_failures(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = resources.ResourceConfig(prefix='QUARTZ')
            for code in (0, 3, 19, 125):
                with self.subTest(code=code), tempfile.TemporaryDirectory(dir=root) as run_directory:
                    receipt = Path(run_directory) / 'graph-build.json'
                    with patch.object(build, 'capped_toolchain', return_value=nullcontext({})) as capped, \
                         patch.object(build, 'run', return_value=code) as guarded:
                        result = build.build(root, ['Quartz.Base'], Path(run_directory), rehash=True,
                                             environment={}, config=config)
                    self.assertEqual(result, code)
                    guarded.assert_called_once()
                    self.assertEqual(guarded.call_args.args,
                                     (['lake', '--rehash', 'build', '+Quartz.Base'],))
                    self.assertEqual(guarded.call_args.kwargs['receipt'], receipt)
                    self.assertEqual(guarded.call_args.kwargs['config'], config)
                    capped.assert_called_once()
                    self.assertEqual(read_json(receipt), {'state': 'reserved'})
                    self.assertFalse((Path(run_directory) / 'cached-check.json').exists())
                    self.assertFalse((Path(run_directory) / 'cached-check.log').exists())

    def test_build_retains_library_selectors_outputs_and_exclusive_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            state = root / 'run'
            outputs = root / 'out/mappings.jsonl'
            with patch.object(build, 'capped_toolchain', return_value=nullcontext({})), \
                 patch.object(build, 'run', return_value=0) as guarded:
                self.assertEqual(build.build(root, ['Quartz'], state, outputs=outputs,
                                             environment={}, selection='library'), 0)
            self.assertEqual(guarded.call_args.args,
                             (['lake', 'build', 'Quartz', '-o', str(outputs.resolve())],))
            receipt = state / 'graph-build.json'
            original = receipt.read_bytes()
            with patch.object(build, 'capped_toolchain') as capped, patch.object(build, 'run') as guarded:
                with self.assertRaises(FileExistsError):
                    build.build(root, ['Quartz'], state, environment={}, selection='library')
                capped.assert_not_called()
                guarded.assert_not_called()
            self.assertEqual(receipt.read_bytes(), original)

    def test_build_rejects_malformed_selector_before_setup(self):
        with tempfile.TemporaryDirectory() as directory, \
             patch.object(build, 'capped_toolchain') as capped, patch.object(build, 'run') as guarded:
            with self.assertRaises(ValueError):
                build.build(Path(directory), ['+Quartz'], Path(directory) / 'run')
            capped.assert_not_called()
            guarded.assert_not_called()

    def test_runtime_direct_process_reuses_prepared_environment_and_valid_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            environment = {'LEAN': '/already/prepared/bin/lean', 'LEAN_NUM_THREADS': '1'}
            runtime = NativeRuntime(root, environment=environment)
            task = {'id': 'native', 'kind': 'process', 'cwd': str(root),
                    'command': ['lake', '--rehash', 'build', 'Quartz']}
            def guarded(command, **keywords):
                self.assertEqual(command, task['command'])
                self.assertEqual(keywords['env'], environment)
                keywords['receipt'].write_text(json.dumps({
                    'state': 'completed', 'command': command, 'cwd': str(root),
                    'exit_code': 0, 'guard_failure': None, 'owned_group_gone': True}))
                return 0
            with patch('lean_tools.runtime.resources.run', side_effect=guarded) as run, \
                 patch.object(build, 'capped_toolchain') as capped, \
                 patch('lean_tools.runtime.subprocess.check_output') as locator:
                result = runtime.run(task, root / 'run')
                run.assert_called_once()
                capped.assert_not_called()
                locator.assert_not_called()
            self.assertEqual(result['receipt']['command'], task['command'])
            self.assertEqual(set(result), {'receipt'})
            with patch('lean_tools.runtime.resources.run') as run:
                with self.assertRaises(FileExistsError):
                    runtime.run(task, root / 'run')
                run.assert_not_called()

    def test_runtime_rejects_failed_incomplete_or_mismatched_process_receipt(self):
        cases = [(19, {}), (0, {'exit_code': 19}), (0, {'guard_failure': 'rss'}),
                 (0, {'owned_group_gone': False}), (0, {'state': 'running'}),
                 (0, {'command': ['different']}), (0, {'cwd': '/different'})]
        for code, override in cases:
            with self.subTest(code=code, override=override), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                task = {'id': 'source', 'kind': 'process', 'cwd': str(root), 'command': ['python3', 'check.py']}
                def guarded(command, **keywords):
                    value = dict(state='completed', command=command, cwd=str(root), exit_code=0,
                                 guard_failure=None, owned_group_gone=True)
                    value.update(override)
                    keywords['receipt'].write_text(json.dumps(value))
                    return code
                with patch('lean_tools.runtime.resources.run', side_effect=guarded):
                    with self.assertRaisesRegex(RuntimeFailure, 'guard/ownership evidence: source'):
                        NativeRuntime(root, environment={}).run(task, root / 'run')

    def test_only_closed_ordinary_exit_is_recoverable(self):
        for code, actual_exit, failure, expected in (
            (19, 19, None, CommandFailed),
            (125, -2, 'watchdog failed closed: KeyboardInterrupt()', RuntimeFailure),
            (143, -15, None, RuntimeFailure)):
            with self.subTest(code=code), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                task = {'id': 'lint', 'kind': 'process', 'cwd': str(root), 'command': ['lake', 'lint']}
                def guarded(command, **keywords):
                    keywords['receipt'].write_text(json.dumps(dict(state='completed', command=command,
                        cwd=str(root), exit_code=actual_exit, guard_failure=failure, owned_group_gone=True)))
                    return code
                with patch('lean_tools.runtime.resources.run', side_effect=guarded), self.assertRaises(expected):
                    NativeRuntime(root, environment={}).run(task, root / 'run')

    def test_runtime_rejects_retired_task_kinds_before_launch(self):
        with tempfile.TemporaryDirectory() as directory, patch('lean_tools.runtime.resources.run') as run:
            for kind in ('build', 'graph-build', 'environment', 'check'):
                with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, 'direct process'):
                    NativeRuntime(directory).run({'kind': kind}, Path(directory) / kind)
            run.assert_not_called()

    def test_managed_identity_binds_wrapper_physical_runtime_and_json_stable_config(self):
        with tempfile.TemporaryDirectory() as directory:
            environment = self.managed(directory)
            physical = Path(directory) / 'physical-runtime'
            (physical / 'bin').mkdir(parents=True)
            (physical / 'lib/lean').mkdir(parents=True)
            for relative in ('bin/lean', 'bin/lake', 'lib/lean/libleanshared.so'):
                (physical / relative).write_bytes(b'fixture actual runtime')
            overlay = Path(environment['LEAN_SYSROOT'])
            (overlay / 'lib').symlink_to(physical / 'lib', target_is_directory=True)
            config = resources.ResourceConfig(profile_keys=('PARENT_PROFILE',))
            observations = TemporalInputs()
            identity = compiler_identity(directory, observations.hash_file, environment=environment,
                                         resource_config=config)
            self.assertEqual(identity, json.loads(json.dumps(identity)))
            self.assertEqual(identity['installation'], str(physical.resolve()))
            self.assertIn(Path(environment['LEAN']).absolute(), observations.files)
            self.assertIn((physical / 'bin/lean').resolve(), observations.files)
            wrapper = Path(environment['LEAN'])
            original = wrapper.read_bytes()
            wrapper.write_bytes(b'transient replacement')
            wrapper.write_bytes(original)
            with self.assertRaisesRegex(ValueError, 'changed'):
                observations.assert_stable()

    def test_managed_unknown_runtime_provenance_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            environment = self.managed(directory)
            with patch('lean_tools.runtime.subprocess.check_output') as locator:
                with self.assertRaisesRegex(ValueError, 'Unsupported managed runtime'):
                    compiler_identity(directory, environment=environment,
                                      resource_config=resources.ResourceConfig(profile_keys=('PARENT_PROFILE',)))
                locator.assert_not_called()

    def test_compiler_override_is_rejected_before_locator(self):
        with patch('lean_tools.runtime.subprocess.check_output') as locator:
            with self.assertRaisesRegex(ValueError, 'LEAN_GITHASH'):
                compiler_identity('.', environment={'LEAN_GITHASH': 'invented'})
            locator.assert_not_called()


if __name__ == '__main__':
    unittest.main()
