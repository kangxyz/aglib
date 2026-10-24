#!/usr/bin/env python3
"""Check dependency cache closure and guarded CI orchestration without Lean."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from lean_tools.cache import mathlib_cache_roots, workspace_imports



class CacheSourceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='quillen-cache-sources-')
        self.root = Path(self.tmp.name)
        self.write('lakefile.toml', 'name = \"quillen-k-theory\"\n')
        self.write('Quillen.lean', 'import Mathlib.Direct\n')

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def test_transitive_aglib_imports_with_modern_modifiers(self):
        self.write('Quillen.lean', 'public meta import all Aglib.First\nimport Mathlib.Direct\n')
        self.write('.lake/packages/Aglib/Aglib/First.lean',
                   'public import Aglib.Second\npublic import Mathlib.First\n')
        self.write('.lake/packages/Aglib/Aglib/Second.lean',
                   'import Aglib.First\nmeta import all Mathlib.Second\n')
        self.write('.lake/packages/Aglib/Aglib/Unused.lean', 'import Mathlib.Unreachable\n')
        self.assertEqual(mathlib_cache_roots(self.root),
                         ['Mathlib.Direct', 'Mathlib.First', 'Mathlib.Second'])

    def test_in_package_tests_and_explicit_client_sources_are_included(self):
        self.write('QuillenTest/Positive.lean', 'import Mathlib.Trust\n')
        self.write('examples/downstream/Consumer.lean', 'import Mathlib.Client\n')
        self.write('examples/downstream/.lake/packages/Bad.lean', 'import Mathlib.Ignored\n')
        self.assertEqual(mathlib_cache_roots(self.root),
                         ['Mathlib.Client', 'Mathlib.Direct', 'Mathlib.Trust'])

    def test_missing_reachable_dependency_fails_closed(self):
        self.write('Quillen.lean', 'import Aglib.Missing\n')
        with self.assertRaisesRegex(ValueError, 'Missing reachable pinned Aglib source'):
            mathlib_cache_roots(self.root)

    def test_explicit_cache_targets_follow_only_their_actual_import_closure(self):
        self.write('Quillen/P.lean', 'import Aglib.P\n')
        self.write('Quillen/Unrelated.lean', 'import Mathlib.Unrelated\n')
        self.write('QuillenTest/T.lean', 'import Quillen.P\nimport Mathlib.Test\n')
        self.write('.lake/packages/Aglib/Aglib/P.lean', 'import Mathlib.Provider\n')
        self.assertEqual(mathlib_cache_roots(self.root, workspace_imports(self.root, ['QuillenTest.T'])),
                         ['Mathlib.Provider', 'Mathlib.Test'])
        with self.assertRaisesRegex(ValueError, 'existing local'):
            workspace_imports(self.root, ['Consumer.Use'])

    def test_root_import_uses_the_pinned_aglib_root(self):
        self.write('Quillen.lean', 'import Aglib\n')
        self.write('.lake/packages/Aglib/Aglib.lean', 'import Aglib.Leaf\n')
        self.write('.lake/packages/Aglib/Aglib/Leaf.lean', 'import Mathlib.Leaf\n')
        self.assertEqual(mathlib_cache_roots(self.root), ['Mathlib.Leaf'])

    def test_empty_scope_never_requests_the_whole_mathlib_cache(self):
        self.write('Quillen.lean', '/- import Mathlib.Hidden -/\n')
        with self.assertRaisesRegex(ValueError, 'unscoped cache download'):
            mathlib_cache_roots(self.root)



if __name__ == '__main__':
    unittest.main()
