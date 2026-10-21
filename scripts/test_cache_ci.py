#!/usr/bin/env python3
"""Check scoped cache orchestration without launching Lake or Lean."""
from contextlib import contextmanager
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from cache_ci import fetch


class ScopedCacheTests(unittest.TestCase):
    def test_only_validated_module_roots_reach_serialized_guarded_cache(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            receipt = root / 'receipt.json'
            calls = []

            @contextmanager
            def capped(actual_root):
                self.assertEqual(actual_root, root)
                yield {'LEAN': '/fixture/capped-lean'}

            with patch('affected_scope.validate') as validate, \
                    patch('affected_scope.cache_roots', return_value=['Mathlib.A', 'Mathlib.B']), \
                    patch('build_serial.capped_toolchain', side_effect=capped), \
                    patch('cache_ci.subprocess.run') as resolve, \
                    patch('resource_guard.run', side_effect=lambda command, **kw: calls.append((command, kw)) or 23):
                self.assertEqual(fetch(root, {'native': True}, receipt), 23)
            validate.assert_called_once_with(root, {'native': True})
            resolve.assert_called_once_with(['lake', 'resolve-deps'], cwd=root, check=True)
            self.assertEqual(calls[0][0][2:],
                             ['--guarded-cache', '/fixture/capped-lean', 'Mathlib.A', 'Mathlib.B'])
            self.assertEqual(calls[0][0][0], sys.executable)
            self.assertEqual(calls[0][1]['receipt'], receipt)
            self.assertEqual(calls[0][1]['cwd'], root)

    def test_docs_scope_skips_dependency_resolution_toolchain_and_cache(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            receipt = root / 'receipt.json'
            with patch('affected_scope.validate'), patch('affected_scope.cache_roots') as roots, \
                    patch('build_serial.capped_toolchain') as capped, \
                    patch('cache_ci.subprocess.run') as resolve, patch('resource_guard.run') as guarded:
                self.assertEqual(fetch(root, {'native': False}, receipt), 0)
            for operation in (roots, capped, resolve, guarded):
                operation.assert_not_called()
            self.assertFalse(receipt.exists())

    def test_missing_scope_or_dependency_inputs_cannot_select_default_cache_get(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with patch('affected_scope.validate', side_effect=ValueError('Missing basis')), \
                    patch('cache_ci.subprocess.run') as resolve, patch('resource_guard.run') as guarded:
                with self.assertRaisesRegex(ValueError, 'Missing basis'):
                    fetch(root, {'native': True}, root / 'receipt.json')
            resolve.assert_not_called()
            guarded.assert_not_called()


if __name__ == '__main__':
    unittest.main()
