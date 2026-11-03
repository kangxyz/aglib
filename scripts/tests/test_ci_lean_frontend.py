"""Job-local compiler selection, effective flags, ownership and signal cleanup."""
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
HELPER = ROOT / '.github/ci-lean-frontend.py'
spec = importlib.util.spec_from_file_location('ci_lean_frontend', HELPER)
frontend = importlib.util.module_from_spec(spec)
spec.loader.exec_module(frontend)


def wait_for(path, process=None, timeout=5):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if path.exists():
            return
        if process is not None and process.poll() is not None:
            raise AssertionError(f'process exited before {path.name}: {process.returncode}')
        time.sleep(0.02)
    raise AssertionError(f'timed out waiting for {path.name}')


class MemoryArguments(unittest.TestCase):
    def test_memory_override_preserves_all_other_flags(self):
        for memory in (['-M12800'], ['-M', '12800'], ['--memory=12800'], ['--memory', '12800']):
            with self.subTest(memory=memory):
                before = ['Main.lean', '-j4', '-DmaxRecDepth=2048', *memory,
                          '--setup', 'setup with spaces.json', '-o', 'Main.olean', '--json']
                expected = ['Main.lean', '-j4', '-DmaxRecDepth=2048', '--setup',
                            'setup with spaces.json', '-o', 'Main.olean', '--json', '-M49152']
                self.assertEqual(frontend.memory_args(before, 49152), expected)
        self.assertEqual(frontend.memory_args(['-M1', '--memory=2', '-j8'], 49152), ['-j8', '-M49152'])

    def test_program_arguments_and_missing_values(self):
        for delimiter in ('--', '--run', '-r'):
            args = ['-M12800', '-j4', delimiter, 'Script.lean', '--memory', 'program argument']
            self.assertEqual(frontend.memory_args(args, 49152),
                             ['-j4', '-M49152', delimiter, 'Script.lean', '--memory', 'program argument'])
        for option in ('-M', '--memory'):
            with self.assertRaisesRegex(ValueError, 'missing memory argument'):
                frontend.memory_args([option], 49152)

    def test_separated_memory_value_cannot_swallow_another_flag_or_source(self):
        for option in ('-M', '--memory'):
            for value in ('-j4', '--run', '-DmaxRecDepth=2048', 'Main.lean'):
                with self.subTest(option=option, value=value):
                    with self.assertRaisesRegex(ValueError, 'invalid memory argument'):
                        frontend.memory_args([option, value, 'Main.lean'], 49152)
            for value in ('0', '0012800'):
                self.assertEqual(frontend.memory_args([option, value, '-j4'], 49152),
                                 ['-j4', '-M49152'])

    def test_default_is_a_complete_noop(self):
        with patch.object(frontend.subprocess, 'run', side_effect=AssertionError('must not find Lean')):
            self.assertEqual(frontend.configure(0), {'enabled': False})
        for heap, aggregate in ((-1, 57344), (49152, 49152), (49152, 13824)):
            with self.assertRaises(ValueError):
                frontend.configure(heap, aggregate)

    def test_effective_aggregate_includes_the_existing_physical_reserve(self):
        with patch.object(frontend.os, 'sysconf', side_effect=lambda key:
                          32768 * 256 if key == 'SC_PHYS_PAGES' else 4096):
            with self.assertRaisesRegex(ValueError, 'effective aggregate'):
                frontend.configure(49152, 57344)


class CompilerProcess(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='ci-lean-frontend-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.toolchain = self.root / 'real toolchain'
        (self.toolchain / 'bin').mkdir(parents=True)
        (self.toolchain / 'lib/lean').mkdir(parents=True)
        (self.toolchain / 'bin/lake').touch()
        self.real = self.toolchain / 'bin/lean'
        self.real.write_text(f'#!{sys.executable}\n' + r'''
import json, os, pathlib, subprocess, sys, time
args = sys.argv[1:]
metadata = {'--print-prefix': str(pathlib.Path(__file__).resolve().parent.parent),
            '--githash': '5045d0056413266e57c625dcd7c365b10e377c52',
            '--version': 'Lean fixture 4.34.1'}
if len(args) == 1 and args[0] in metadata:
    print(metadata[args[0]])
    raise SystemExit(0)
if '--run' in args or '-r' in args:
    raise SystemExit(subprocess.run(json.loads(os.environ['FIXTURE_NESTED_COMMAND'])).returncode)
record = pathlib.Path(os.environ['FIXTURE_RECORD'])
record.write_text(json.dumps({'args': args, 'pid': os.getpid()}))
gate = pathlib.Path(os.environ['FIXTURE_GATE'])
while not gate.exists():
    time.sleep(0.02)
''')
        self.real.chmod(0o700)
        self.setup = self.configure('first')

    def configure(self, name):
        with patch.object(frontend.os, 'sysconf', side_effect=lambda key:
                          65536 * 256 if key == 'SC_PHYS_PAGES' else 4096):
            return frontend.configure(49152, 57344, self.real, self.root,
                                      self.root / (name + '.env'), self.root / (name + '.path'))

    def start(self, name, setup=None):
        setup = setup or self.setup
        record, gate = self.root / (name + '.json'), self.root / (name + '.gate')
        process = subprocess.Popen([setup['environment']['LEAN'], name + '.lean', '-M12800', '-j4'],
            env={**os.environ, 'FIXTURE_RECORD': str(record), 'FIXTURE_GATE': str(gate)},
            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)

        def stop():
            if process.poll() is None:
                process.kill()
            process.communicate(timeout=5)
        self.addCleanup(stop)
        return process, record, gate

    def test_real_process_receives_effective_flags_and_metadata_bypasses_lock(self):
        process, record, gate = self.start('first')
        wait_for(record, process)
        self.assertEqual(json.loads(record.read_text())['args'], ['first.lean', '-j4', '-M49152'])
        # Exec keeps the PID and lock ownership in the compiler, without a supervisor.
        self.assertEqual(json.loads(record.read_text())['pid'], process.pid)
        for argument in ('--print-prefix', '--githash', '--version'):
            expected = subprocess.run([str(self.real), argument], capture_output=True, text=True, check=True)
            observed = subprocess.run([self.setup['environment']['LEAN'], argument],
                                      capture_output=True, text=True, timeout=3, check=True)
            self.assertEqual(observed.stdout, expected.stdout)
            self.assertEqual(observed.stderr, '')
        gate.touch()
        self.assertEqual(process.wait(timeout=5), 0)

    def test_only_one_compiler_per_job_and_other_jobs_are_independent(self):
        first, one, gate_one = self.start('one')
        wait_for(one, first)
        second, two, gate_two = self.start('two')
        other, other_record, other_gate = self.start('other', self.configure('other'))
        wait_for(other_record, other)
        self.assertFalse(two.exists())
        self.assertIsNone(second.poll())
        gate_one.touch()
        self.assertEqual(first.wait(timeout=5), 0)
        wait_for(two, second)
        gate_two.touch()
        other_gate.touch()
        self.assertEqual(second.wait(timeout=5), 0)
        self.assertEqual(other.wait(timeout=5), 0)

    def test_termination_releases_compiler_slot(self):
        for signum in (signal.SIGTERM, signal.SIGKILL):
            with self.subTest(signal=signum):
                first, one, _ = self.start(f'owner-{signum}')
                wait_for(one, first)
                second, two, gate = self.start(f'waiter-{signum}')
                time.sleep(0.1)
                self.assertFalse(two.exists())
                first.send_signal(signum)
                self.assertEqual(first.wait(timeout=5), -signum)
                wait_for(two, second)
                gate.touch()
                self.assertEqual(second.wait(timeout=5), 0)

    def test_killed_waiter_does_not_release_the_live_owner(self):
        first, one, gate_one = self.start('owner')
        wait_for(one, first)
        waiter, waiter_record, _ = self.start('cancelled-waiter')
        time.sleep(0.1)
        waiter.terminate()
        waiter.wait(timeout=5)
        third, third_record, gate_three = self.start('third')
        time.sleep(0.15)
        self.assertFalse(waiter_record.exists())
        self.assertFalse(third_record.exists())
        gate_one.touch()
        first.wait(timeout=5)
        wait_for(third_record, third)
        gate_three.touch()
        self.assertEqual(third.wait(timeout=5), 0)

    def test_run_control_program_can_launch_a_wrapped_compiler(self):
        record, gate = self.root / 'nested.json', self.root / 'nested.gate'
        gate.touch()
        command = [self.setup['environment']['LEAN'], 'Nested.lean', '-M12800', '-j4']
        result = subprocess.run([self.setup['environment']['LEAN'], '--run', 'Control.lean'],
            env={**os.environ, 'FIXTURE_NESTED_COMMAND': json.dumps(command),
                 'FIXTURE_RECORD': str(record), 'FIXTURE_GATE': str(gate)},
            capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(record.read_text())['args'], ['Nested.lean', '-j4', '-M49152'])

    def test_replaced_or_symlinked_lock_fails_closed(self):
        runtime = Path(self.setup['runtime'])
        lock = runtime / 'frontend.lock'
        original = runtime / 'original.lock'
        lock.rename(original)
        lock.touch()
        process, record, _ = self.start('replaced')
        self.assertEqual(process.wait(timeout=5), 2)
        self.assertFalse(record.exists())
        lock.unlink()
        lock.symlink_to(original)
        process, record, _ = self.start('symlinked')
        self.assertEqual(process.wait(timeout=5), 2)
        self.assertFalse(record.exists())


@unittest.skipUnless(os.environ.get('CI_LEAN_FRONTEND_TEST_TOOLCHAIN'),
                     'Set CI_LEAN_FRONTEND_TEST_TOOLCHAIN for the tiny pinned-Lake tooling fixture')
class PinnedLakeSelection(unittest.TestCase):
    def test_real_lake_selects_wrapper_and_reuses_existing_weak_arg_outputs(self):
        toolchain = Path(os.environ['CI_LEAN_FRONTEND_TEST_TOOLCHAIN']).resolve()
        lean, lake = toolchain / 'bin/lean', toolchain / 'bin/lake'
        self.assertEqual(subprocess.check_output([str(lean), '--githash'], text=True).strip(),
                         '5045d0056413266e57c625dcd7c365b10e377c52')
        with tempfile.TemporaryDirectory(prefix='ci-pinned-lake-') as directory:
            root = Path(directory)
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            (root / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\n'
                'package frontendFixture where\n  weakLeanArgs := #["-M12800", "-j4"]\n'
                'lean_lib Probe\nlean_lib Fresh\n')
            for name in ('Probe', 'Fresh'):
                (root / (name + '.lean')).write_text('import Lake\ndef answer : Nat := 42\n')
            environment = {key: value for key, value in os.environ.items()
                           if key not in {'LEAN', 'LEAN_SYSROOT', 'LEAN_GITHASH', 'LAKE',
                                          'LAKE_HOME', 'LAKE_OVERRIDE_LEAN', 'ELAN_TOOLCHAIN'}}
            environment.update(LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='false',
                               LAKE_CACHE_DIR=str(root / 'cache'))

            def invoke(arguments, env):
                result = subprocess.run([str(lake), *arguments], cwd=root, env=env,
                                        capture_output=True, text=True, timeout=60)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                return result

            invoke(['--rehash', 'build', 'Probe'], environment)
            artifact = root / '.lake/build/lib/lean/Probe.olean'
            before = (artifact.read_bytes(), artifact.stat().st_mtime_ns)
            configured = frontend.configure(49152, 57344, lean, root, root / 'env', root / 'path')
            wrapped = {**environment, **configured['environment']}
            wrapped['PATH'] = str(Path(configured['environment']['LEAN']).parent) + os.pathsep + environment['PATH']
            reused = invoke(['--no-build', '--rehash', 'build', 'Probe'], wrapped)
            self.assertNotIn('ci-lean-frontend:', reused.stdout + reused.stderr)
            self.assertEqual((artifact.read_bytes(), artifact.stat().st_mtime_ns), before)
            fresh = invoke(['--rehash', 'build', 'Fresh'], wrapped)
            self.assertIn('ci-lean-frontend: one compiler, effective -M49152', fresh.stdout + fresh.stderr)
            self.assertTrue((root / '.lake/build/lib/lean/Fresh.olean').is_file())
            for argument in ('--print-prefix', '--githash', '--version'):
                expected = subprocess.check_output([str(lean), argument], text=True)
                actual = subprocess.check_output([configured['environment']['LEAN'], argument], env=wrapped, text=True)
                self.assertEqual(actual, expected)


if __name__ == '__main__':
    unittest.main()
