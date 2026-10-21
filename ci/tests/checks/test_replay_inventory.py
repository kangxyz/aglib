"""Generic package/config coordinates and explicit replay scope, without Lean."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from lean_ci.checks import replay
from lean_ci.checks.replay_inventory import load_inventory, check_inventory


class ReplayInventoryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name).resolve()
        self.write('lean/lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('lean/lakefile.toml', 'name="PackageSlug"\nsrcDir="src"\n[[lean_lib]]\nname="Core"\n[[lean_lib]]\nname="Checks"\n')
        self.write('lean/src/Core.lean', 'module\n')
        self.write('lean/src/Checks.lean', 'module\n')
        self.write('lean/src/Checks/Adoption.lean', 'import Core\n')
        self.write('lean/src/Checks/Negative.lean', 'axiom bad : False\n')
        self.write('client/lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('client/lakefile.toml', 'name="IndependentPackage"\n[[lean_lib]]\nname="Client"\n')
        self.write('client/Client.lean', 'module\n')
        self.write('.github/lean-ci.toml', 'schema=1\npackage_dir="lean"\n'
                   'formal_only=["lean/src/Checks/Adoption.lean"]\n'
                   'expected_failure=["lean/src/Checks/Negative.lean"]\n'
                   '[roles]\nproduction=["Core"]\ntests=["Checks"]\n'
                   '[[clients]]\nid="example"\npath="client"\n'
                   '[clients.roles]\nproduction=["Client"]\n')

    def write(self, path, value):
        p = self.repo / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(value)

    def test_nested_package_srcdir_and_client_identity_are_not_library_names(self):
        root = load_inventory(self.repo, workspace='root')
        self.assertEqual(root.root, self.repo / 'lean')
        self.assertEqual(root.expected_sources(), {Path('src/Core.lean'), Path('src/Checks.lean')})
        self.assertEqual(root.names(root.expected_sources()), ['Checks', 'Core'])
        client = load_inventory(self.repo, workspace='example')
        self.assertEqual(client.root, self.repo / 'client')
        self.assertEqual(client.names(client.expected_sources()), ['Client'])

    def test_explicit_formal_scope_does_not_become_positive_or_admit_negative(self):
        catalog = load_inventory(self.repo, workspace='root')
        self.assertEqual(catalog.source('Checks.Adoption'), Path('src/Checks/Adoption.lean'))
        self.assertNotIn(catalog.source('Checks.Adoption'), catalog.expected_sources())
        with self.assertRaisesRegex(RuntimeError, 'Unenrolled'):
            catalog.source('Checks.Negative')
        self.write('lean/.lake/build/lib/lean/Checks/Adoption.olean', 'compiled')
        self.assertEqual(check_inventory(catalog.root, ['Checks.Adoption'], inventory=catalog), [])

    def test_selected_inventory_ignores_missing_peers_but_rejects_stale_outputs(self):
        catalog = load_inventory(self.repo, workspace='root')
        self.write('lean/.lake/build/lib/lean/Core.olean', 'compiled')
        self.assertEqual(check_inventory(catalog.root, ['Core'], inventory=catalog), [])
        self.write('lean/.lake/build/lib/lean/Core/Deleted.olean', 'stale')
        self.assertTrue(check_inventory(catalog.root, ['Core'], inventory=catalog))

    def test_omitted_selection_stops_before_environment_or_receipt_writes(self):
        with patch.object(replay, 'lake_environment') as environment:
            with self.assertRaisesRegex(ValueError, 'explicit'):
                replay.replay(self.repo / 'lean', self.repo / 'receipts')
        environment.assert_not_called()
        self.assertFalse((self.repo / 'receipts').exists())

    def test_cli_resolves_configured_client_then_forwards_explicit_scope(self):
        with patch.object(replay, 'replay') as run:
            self.assertEqual(replay.main(['--root', str(self.repo), '--workspace', 'example',
                '--receipt-dir', str(self.repo / 'receipts'), '--modules', 'Client']), 0)
        args, kwargs = run.call_args
        self.assertEqual(args[0], self.repo / 'client')
        self.assertEqual(kwargs['selected'], ['Client'])
        self.assertFalse(kwargs['whole_scope'])

    def test_support_catalog_is_explicit_and_cannot_promote_negative_or_formal(self):
        config = self.repo / '.github/lean-ci.toml'
        config.write_text(config.read_text() + '\n[policy]\ninventory=[".github/inventory.json"]\n')
        for value in ('lean/src/Checks/Adoption.lean', 'lean/src/Checks/Negative.lean', 'missing.lean'):
            self.write('.github/inventory.json', json.dumps({'schema': 1, 'kind': 'inventory',
                       'included_support': [value]}))
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, 'cannot promote'):
                load_inventory(self.repo, workspace='root').expected_sources()

    def test_explicit_compile_pass_support_retains_control_role(self):
        self.write('lean/src/Checks/Helper.lean', 'import Core\n')
        config = self.repo / '.github/lean-ci.toml'
        config.write_text(config.read_text().replace('[roles]',
            'controls=["lean/src/Checks/Helper.lean"]\n[roles]') +
            '\n[policy]\ninventory=[".github/inventory.json"]\n')
        self.write('.github/inventory.json', json.dumps({'schema': 1, 'kind': 'inventory',
                   'included_support': ['lean/src/Checks/Helper.lean']}))
        catalog = load_inventory(self.repo, workspace='root')
        self.assertIn(Path('src/Checks/Helper.lean'), catalog.expected_sources())
        self.assertEqual(catalog.rows['Checks.Helper']['role'], 'control')


if __name__ == '__main__':
    unittest.main()
