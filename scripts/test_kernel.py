"""Controller tests with fake artifacts and markers; never execute Lean."""
from contextlib import redirect_stdout
import io
import json
import os
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
        for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
            (root / name).write_text('fixed config')
        for name in ['lib/lean/LeanChecker.olean', 'src/lean/LeanChecker.lean']:
            (prefix / name).parent.mkdir(parents=True, exist_ok=True)
            (prefix / name).write_text('fixed checker')
        return root, prefix, sources

    def patched(self, prefix, sources):
        from contextlib import ExitStack
        stack = ExitStack()
        stack.enter_context(patch.object(kernel, 'check_inventory', return_value=[]))
        stack.enter_context(patch.object(kernel, 'expected_sources', return_value=sources))
        stack.enter_context(patch.object(kernel, 'lake_environment', return_value={'lean': '/pinned/lean'}))
        stack.enter_context(patch.object(kernel.subprocess, 'check_output', return_value=str(prefix)))
        stack.enter_context(patch.object(kernel.os, 'cpu_count', return_value=8))
        stack.enter_context(redirect_stdout(io.StringIO()))
        return stack

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
                original = kernel.record_path(directory, sorted(map(kernel.module_name, sources)), 'Aglib.One').read_bytes()
                kernel.replay(root, directory, batch_size=2)
                self.assertEqual(calls, [['Aglib.One'], ['Aglib', 'AglibTest']])
                self.assertEqual(json.loads((directory / 'coverage.json').read_text())['covered_modules'], 3)
                self.assertEqual(kernel.record_path(directory, sorted(map(kernel.module_name, sources)), 'Aglib.One').read_bytes(), original)
                self.assertNotIn('limits', json.loads((directory / 'basis.json').read_text()))
                (root / 'Aglib/One.lean').write_text('changed source')
                with self.assertRaisesRegex(RuntimeError, 'basis changed'):
                    kernel.replay(root, directory, batch_size=4)

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

    def test_client_stale_artifact_rejected_before_replay(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); (root / 'Consumer.lean').write_text('module\n')
            library = root / '.lake/build/lib/lean'; (library / 'Consumer').mkdir(parents=True)
            (library / 'Consumer.olean').write_bytes(b'current')
            (library / 'Consumer/Deleted.olean').write_bytes(b'stale')
            with self.assertRaisesRegex(RuntimeError, 'inventory'):
                kernel.proof_basis(root, root, client=True)

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
