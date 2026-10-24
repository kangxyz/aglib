# Authors: kangxyz
"""Independent-client cache ownership and guarded acceptance fixtures, without Lean."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from lean_tools.motivic.client import prepare


class ClientBuildTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='motivic client ')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.client = self.root / 'examples/downstream'
        self.client.mkdir(parents=True)
        self.packages = self.root / '.lake/packages'
        self.packages.mkdir(parents=True)
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:fixture\n')
        (self.client / 'lean-toolchain').write_text('leanprover/lean4:fixture\n')
        (self.client / 'MotivicClient.lean').write_text('module\npublic import Motivic\n')
        (self.client / 'lakefile.toml').write_text('''name = "MotivicClient"
[[lean_lib]]
name = "MotivicClient"
leanOptions = {autoImplicit = false, warningAsError = true}
[[require]]
name = "Motivic"
path = "../.."
''')
        self.manifest = {'name': 'Motivic', 'version': '1.2.0', 'lakeDir': '.lake',
            'packagesDir': '.lake/packages', 'packages': [
                {'name': 'Aglib', 'type': 'git', 'rev': 'locked-aglib', 'inherited': False},
                {'name': 'mathlib', 'type': 'git', 'rev': 'locked-mathlib', 'inherited': False}]}
        (self.root / 'lake-manifest.json').write_text(json.dumps(self.manifest) + '\n')

    def test_inherits_exact_pins_and_shares_only_this_checkout_packages(self):
        original = (self.root / 'lake-manifest.json').read_bytes()
        self.assertEqual(prepare(self.root), self.client)
        manifest = json.loads((self.client / 'lake-manifest.json').read_text())
        self.assertEqual(manifest['name'], 'MotivicClient')
        self.assertEqual([(r['name'], r['rev'], r['inherited']) for r in manifest['packages'][:-1]],
                         [('Aglib', 'locked-aglib', True), ('mathlib', 'locked-mathlib', True)])
        self.assertEqual(manifest['packages'][-1]['dir'], '../..')
        self.assertEqual((self.client / '.lake/packages').resolve(), self.packages)
        self.assertFalse((self.client / '.lake/build').is_symlink())
        self.assertEqual((self.root / 'lake-manifest.json').read_bytes(), original)
        prepare(self.root)  # Repeated preparation preserves the same owned cache.

    def test_rejects_foreign_packages_without_overwriting_user_state(self):
        (self.client / '.lake').mkdir()
        foreign = self.root / 'foreign-packages'
        foreign.mkdir()
        (self.client / '.lake/packages').symlink_to(foreign, target_is_directory=True)
        manifest = self.client / 'lake-manifest.json'
        manifest.write_text('user manifest\n')
        with self.assertRaisesRegex(ValueError, 'foreign cache'):
            prepare(self.root)
        self.assertEqual(manifest.read_text(), 'user manifest\n')
        self.assertEqual((self.client / '.lake/packages').resolve(), foreign)

    def test_rejects_shared_build_outputs_and_toolchain_drift(self):
        (self.client / 'lean-toolchain').write_text('different\n')
        with self.assertRaisesRegex(ValueError, 'same pinned'):
            prepare(self.root)
        (self.client / 'lean-toolchain').write_text('leanprover/lean4:fixture\n')
        (self.client / '.lake').mkdir()
        (self.client / '.lake/build').symlink_to(self.root / 'foreign-build')
        with self.assertRaisesRegex(ValueError, 'owned directories'):
            prepare(self.root)

    def test_explicit_client_uses_shared_module_builder(self):
        from lean_tools.motivic import client as build_client
        from unittest.mock import patch
        receipt = self.root / 'receipt'
        with patch.object(sys, 'argv', ['build_client.py', '--root', str(self.root),
                                       '--receipt-dir', str(receipt)]), \
                patch('lean_tools.build.build', return_value=9) as build:
            self.assertEqual(build_client.main(), 9)
        self.assertEqual(build.call_args.args, (self.client, ['MotivicClient'], receipt))
        self.assertEqual(build.call_args.kwargs['selection'], 'module')
        self.assertTrue(build.call_args.kwargs['rehash'])


if __name__ == '__main__':
    unittest.main()
