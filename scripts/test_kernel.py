"""Exact-module enrollment/resume tests with fake artifacts, never executing Lean."""
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from contextlib import redirect_stdout
import io

import check_kernel as kernel


class KernelTests(unittest.TestCase):
    def test_client_stale_artifact_rejected_before_any_lean_lookup(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'Consumer.lean').write_text('module\n')
            library = root / '.lake/build/lib/lean'
            (library / 'Consumer').mkdir(parents=True)
            (library / 'Consumer.olean').write_bytes(b'current')
            (library / 'Consumer/Deleted.olean').write_bytes(b'stale')
            with patch.object(kernel, 'lake_environment') as lookup:
                with self.assertRaisesRegex(RuntimeError, 'inventory'):
                    kernel.replay(root, root / 'receipts', client=True)
                lookup.assert_not_called()

    def test_driver_imports_fixed_semantics_without_fanout_entrypoint(self):
        self.assertIn('import LeanChecker', kernel.DRIVER)
        self.assertIn('replayFromImports name', kernel.DRIVER)
        self.assertIn('parts[parts.size - 1].1.constNames.size', kernel.DRIVER)
        self.assertNotIn('IO.asTask', kernel.DRIVER)
        self.assertNotIn('def main', kernel.DRIVER)
        self.assertNotIn('--run', kernel.DRIVER)
        self.assertNotIn('replayFromFresh', kernel.DRIVER)

    def test_probe_then_resume_covers_exact_set_once_and_rejects_changed_basis(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'root'; prefix = Path(temporary) / 'toolchain'
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
                (prefix / name).write_text('fixed installed checker')
            calls = []
            def guarded(command, **kwargs):
                self.assertNotIn('--run', command)
                self.assertIn('-j1', command)
                self.assertTrue(any(arg.startswith('-M') for arg in command))
                name = kwargs['env']['AGLIB_KERNEL_MODULE']; calls.append(name)
                count = 2 if name == 'Aglib.One' else 0
                os.write(1, f'AGLIB_KERNEL_CHECKED {name} {count}\n'.encode())
                return 0
            directory = Path(temporary) / 'receipts'
            with patch.object(kernel, 'check_inventory', return_value=[]), \
                    patch.object(kernel, 'expected_sources', return_value=sources), \
                    patch.object(kernel, 'lake_environment', return_value={'lean': '/pinned/lean'}), \
                    patch.object(kernel.subprocess, 'check_output', return_value=str(prefix)), \
                    patch.object(kernel, 'run', side_effect=guarded), \
                    redirect_stdout(io.StringIO()):
                kernel.replay(root, directory, only='Aglib.One')
                self.assertEqual(json.loads((directory / 'probe.json').read_text())['covered_modules'], 1)
                self.assertFalse((directory / 'coverage.json').exists())
                kernel.replay(root, directory)
                result = json.loads((directory / 'coverage.json').read_text())
                self.assertEqual(result['covered_modules'], 3)
                self.assertEqual(result['vacuous_modules'], 2)
                self.assertEqual(sorted(calls), ['Aglib', 'Aglib.One', 'AglibTest'])
                (root / 'Aglib/One.lean').write_text('changed source')
                with self.assertRaisesRegex(RuntimeError, 'basis changed'):
                    kernel.replay(root, directory)


if __name__ == '__main__':
    unittest.main()
