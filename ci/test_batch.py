"""Bounded native-check scheduling tests; no Lean, Git or remote execution."""
from concurrent.futures import wait as real_wait
from contextlib import nullcontext, redirect_stderr
import io
from pathlib import Path
import sys
import tempfile
import threading
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from lean_ci.batch import check_group, run_checks
from lean_ci import resources
from lean_ci.resources import ResourceConfig
from lean_ci.runtime import NativeRuntime
from lean_ci.state import Progress, read_json, write_json


def task(index=0, jobs=2, **changes):
    return dict(id='origin/' + str(index), kind='check', cwd='/fixture',
                command=['python3', 'checker.py', '--no-build', str(index)],
                modules=['Origin' + str(index)], capped=True,
                check_batch={'id': 'origins', 'jobs': jobs, 'read_only': True,
                             'single_process': True}, **changes)


def evidence(item):
    return {'receipt': {'state': 'completed', 'command': item['command'],
            'cwd': item['cwd'], 'exit_code': 0, 'guard_failure': None,
            'owned_group_gone': True}}


class ControlledExecutor:
    def __init__(self, *, fail=None, callback=None):
        self.fail, self.callback = fail, callback
        self.lock, self.active, self.peak = threading.Lock(), 0, 0
        self.calls, self.worker_threads = [], set()

    def run(self, item, directory, *, cancelled=None):
        with self.lock:
            self.active += 1
            self.peak = max(self.peak, self.active)
            self.calls.append(item['id'])
            self.worker_threads.add(threading.get_ident())
        try:
            if self.callback:
                self.callback(item)
            time.sleep(0.005 if item['id'] == 'origin/0' else 0.04)
            if item['id'] == self.fail:
                raise ValueError('synthetic native failure')
            return evidence(item)
        finally:
            with self.lock:
                self.active -= 1


class BatchTests(unittest.TestCase):
    def setUp(self):
        self.runtime = SimpleNamespace(environment={}, resource_config=ResourceConfig())
        self.temporary = tempfile.TemporaryDirectory(prefix='lean-check-batch-')
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)

    def pending(self, count):
        return [(index, task(index), self.directory / str(index)) for index in range(count)]

    def test_profile_admission_and_local_serial_policy(self):
        self.assertEqual(check_group([task(jobs=1)], self.runtime), 1)
        with self.assertRaisesRegex(ValueError, 'resource profile'):
            check_group([task()], self.runtime)
        profile = {'jobs': 3}
        with patch('lean_ci.batch.resources.remote_profile', return_value=profile) as observed:
            self.assertEqual(check_group([task(0), task(1)], self.runtime), 2)
            observed.assert_called_with(self.runtime.environment, self.runtime.resource_config)
            with self.assertRaisesRegex(ValueError, 'resource profile'):
                check_group([task(jobs=4)], self.runtime)

    def test_rejects_malformed_or_mutating_groups(self):
        forbidden = ('generated', 'generated_path', 'mapping', 'identity_modules',
                     'establishes_inputs', 'established_paths', 'environment_output')
        for field in forbidden:
            with self.subTest(field=field), self.assertRaises(ValueError):
                check_group([dict(task(jobs=1), **{field: ['write']})], self.runtime)
        for change in ({'kind': 'build'}, {'kind': 'environment'}, {'capped': False},
                       {'native': False}, {'check_batch': {'id': 'x', 'jobs': True}}):
            with self.subTest(change=change), self.assertRaises(ValueError):
                check_group([dict(task(jobs=1), **change)], self.runtime)
        with self.assertRaises(ValueError):
            check_group([task(jobs=1), task(jobs=1)], self.runtime)
        with self.assertRaises(ValueError):
            check_group([task(jobs=1), task(1, jobs=2)], self.runtime)

    def test_bounded_overlap_and_coordinator_only_callback(self):
        barrier = threading.Barrier(2, timeout=2)
        executor = ControlledExecutor(callback=lambda item: barrier.wait())
        owner, callbacks = threading.get_ident(), []
        run_checks(executor, self.pending(4), 2,
                   lambda index, result: callbacks.append((index, threading.get_ident())))
        self.assertEqual(executor.peak, 2)
        self.assertEqual(executor.active, 0)
        self.assertEqual(sorted(index for index, _ in callbacks), list(range(4)))
        self.assertEqual({thread for _, thread in callbacks}, {owner})
        self.assertNotIn(owner, executor.worker_threads)

    def test_failure_retains_individual_success_and_stops_admission(self):
        barrier = threading.Barrier(2, timeout=2)
        executor = ControlledExecutor(fail='origin/0', callback=lambda item: barrier.wait())
        progress, pending = Progress(self.directory / 'progress'), self.pending(5)
        bindings = {index: {'arguments': item['command'], 'basis': 'stable'}
                    for index, item, _ in pending}

        def accept(index, result):
            receipt = result['receipt']
            progress.save(bindings[index], receipt, receipt['command'])

        with self.assertRaisesRegex(ValueError, 'synthetic native failure'):
            run_checks(executor, pending, 2, accept)
        self.assertEqual(set(executor.calls), {'origin/0', 'origin/1'})
        self.assertEqual(executor.active, 0)
        self.assertIsNone(progress.lookup(bindings[0]))
        self.assertIsNotNone(progress.lookup(bindings[1]))
        self.assertIsNone(progress.lookup(dict(bindings[1], basis='changed')))

    def test_postbinding_failure_does_not_discard_peer_success(self):
        barrier = threading.Barrier(2, timeout=2)
        executor = ControlledExecutor(callback=lambda item: barrier.wait())
        accepted = []

        def accept(index, result):
            if index == 0:
                raise ValueError('synthetic binding drift')
            accepted.append(index)

        with self.assertRaisesRegex(ValueError, 'binding drift'):
            run_checks(executor, self.pending(4), 2, accept)
        self.assertEqual(accepted, [1])
        self.assertEqual(set(executor.calls), {'origin/0', 'origin/1'})
        self.assertEqual(executor.active, 0)

    def test_interruption_drains_and_accepts_active_successes(self):
        barrier = threading.Barrier(2, timeout=2)
        executor = ControlledExecutor(callback=lambda item: barrier.wait())
        accepted, wait_calls = [], []

        def interrupted_once(*args, **kwargs):
            wait_calls.append(True)
            if len(wait_calls) == 1:
                raise KeyboardInterrupt()
            return real_wait(*args, **kwargs)

        with patch('lean_ci.batch.wait', side_effect=interrupted_once):
            with self.assertRaises(KeyboardInterrupt):
                run_checks(executor, self.pending(4), 2,
                           lambda index, result: accepted.append(index))
        self.assertEqual(set(accepted), {0, 1})
        self.assertEqual(set(executor.calls), {'origin/0', 'origin/1'})
        self.assertEqual(executor.active, 0)

    def test_invalid_job_cap_never_launches(self):
        executor = ControlledExecutor()
        for jobs in (0, -1, True, 1.5):
            with self.subTest(jobs=jobs), self.assertRaises(ValueError):
                run_checks(executor, self.pending(1), jobs, lambda *args: None)
        self.assertEqual(executor.calls, [])

    def test_pending_generator_failure_retains_completed_peer(self):
        executor, accepted = ControlledExecutor(), []

        def pending():
            yield self.pending(1)[0]
            raise ValueError('coordinator prebinding failed')

        with self.assertRaisesRegex(ValueError, 'coordinator prebinding failed'):
            run_checks(executor, pending(), 2,
                       lambda index, result: accepted.append(index))
        self.assertEqual(accepted, [0])
        self.assertEqual(executor.calls, ['origin/0'])
        self.assertEqual(executor.active, 0)

    def test_pending_generator_interrupt_cancels_and_drains_active_peer(self):
        started, stopped = threading.Event(), threading.Event()

        class CancellableExecutor:
            def run(self, item, directory, *, cancelled):
                started.set()
                deadline = time.monotonic() + 2
                while not cancelled() and time.monotonic() < deadline:
                    time.sleep(0.002)
                stopped.set()
                if not cancelled():
                    raise AssertionError('Generator interrupt did not request cancellation')
                raise ValueError('cancelled native call')

        def pending():
            yield self.pending(1)[0]
            self.assertTrue(started.wait(timeout=2))
            raise KeyboardInterrupt()

        with self.assertRaises(KeyboardInterrupt):
            run_checks(CancellableExecutor(), pending(), 2, lambda *args: None)
        self.assertTrue(stopped.is_set())

    def test_interrupt_requests_native_cancellation_and_drains_workers(self):
        started = threading.Barrier(3, timeout=2)
        stopped = []

        class CancellableExecutor:
            def run(self, item, directory, *, cancelled):
                started.wait()
                deadline = time.monotonic() + 2
                while not cancelled() and time.monotonic() < deadline:
                    time.sleep(0.002)
                stopped.append(item['id'])
                if not cancelled():
                    raise AssertionError('Native cancellation was not requested')
                raise ValueError('cancelled native call')

        def interrupt_after_start(*args, **kwargs):
            started.wait()
            raise KeyboardInterrupt()

        waits = 0

        def controlled_wait(*args, **kwargs):
            nonlocal waits
            waits += 1
            if waits == 1:
                return interrupt_after_start(*args, **kwargs)
            return real_wait(*args, **kwargs)

        with patch('lean_ci.batch.wait', side_effect=controlled_wait):
            with self.assertRaises(KeyboardInterrupt):
                run_checks(CancellableExecutor(), self.pending(5), 2, lambda *args: None)
        self.assertEqual(set(stopped), {'origin/0', 'origin/1'})

    def test_cancelled_resource_call_never_launches(self):
        budget = resources.limits({}, 8 * 1024**3)
        with patch.object(resources.subprocess, 'Popen') as launch:
            with self.assertRaisesRegex(InterruptedError, 'before launch'):
                resources.run([sys.executable, '-c', 'pass'], env={}, budget=budget,
                              sampler=lambda group: [], cancelled=lambda: True)
            launch.assert_not_called()

    def test_runtime_forwards_cancellation_with_unchanged_environment_and_caps(self):
        runtime = NativeRuntime(self.directory, ResourceConfig(prefix='FIXTURE'),
                                {'PRESERVED': 'managed-wrapper-context'})
        item = dict(task(jobs=1), cwd=str(self.directory))
        budget, cancellation = {'native': 'fixture-budget'}, lambda: False
        selected = dict(runtime.environment, LEAN='selected-wrapper')

        def run(command, **kwargs):
            self.assertIs(kwargs['cancelled'], cancellation)
            self.assertEqual(kwargs['env'], selected)
            self.assertIs(kwargs['config'], runtime.resource_config)
            self.assertEqual(kwargs['budget'], dict(budget, native_build_threads=1))
            write_json(kwargs['receipt'], evidence(item)['receipt'])
            return 0

        with patch('lean_ci.runtime.resources.limits', return_value=budget), \
             patch('lean_ci.runtime.build.build_threads', return_value=1), \
             patch('lean_ci.runtime.build.capped_toolchain', return_value=nullcontext(selected)), \
             patch('lean_ci.runtime.resources.run', side_effect=run):
            runtime.run(item, self.directory / 'run', cancelled=cancellation)
        self.assertEqual(runtime.environment, {'PRESERVED': 'managed-wrapper-context'})

    def test_actual_cancelled_owned_group_and_descendant_are_settled(self):
        marker, receipt = self.directory / 'descendant.pid', self.directory / 'cancelled.json'
        program = ('import pathlib,signal,subprocess,sys,time\n'
                   'child=subprocess.Popen([sys.executable,"-c","import time; time.sleep(30)"])\n'
                   'def stop(*args):\n child.wait(timeout=2)\n sys.exit(0)\n'
                   'signal.signal(signal.SIGTERM,stop)\n'
                   f'pathlib.Path({str(marker)!r}).write_text(str(child.pid))\n'
                   'time.sleep(30)\n')
        budget = resources.limits({}, 8 * 1024**3)
        started, deadline = time.monotonic(), time.monotonic() + 3
        with redirect_stderr(io.StringIO()):
            code = resources.run([sys.executable, '-c', program], env={}, budget=budget,
                                 receipt=receipt,
                                 cancelled=lambda: marker.exists() or time.monotonic() > deadline)
        actual = read_json(receipt)
        self.assertEqual(code, 125)
        self.assertTrue(marker.exists())
        self.assertEqual(actual['guard_failure'], 'owned process group cancelled')
        self.assertTrue(actual['owned_group_gone'])
        self.assertEqual(resources.group_processes(actual['pgid']), [])
        self.assertLess(time.monotonic() - started, 5)


if __name__ == '__main__':
    unittest.main()
