# Authors: kangxyz
"""Semantic-selector forwarding against the shared core; never invoke Lean."""
from contextlib import contextmanager, redirect_stderr
import io
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from lean_ci.motivic.build import command
from lean_ci.motivic import build as module_build



class BuildForwardingTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for name in ('Motivic', 'MotivicTest', 'Motivic.Selected'):
            path = self.root.joinpath(*name.split('.')).with_suffix('.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('module\n')

    def test_public_wrapper_passes_bare_names_and_optional_export_to_core_launcher(self):
        for export in (False, True):
            outputs = self.root / 'outputs.jsonl'
            argv = command(self.root, ['Motivic', 'MotivicTest'], self.root / 'receipts',
                           outputs=outputs, export_only=export)
            self.assertEqual(argv[1:4], ['-m', 'lean_ci', 'build'])
            self.assertEqual(argv[-2:], ['Motivic', 'MotivicTest'])
            self.assertEqual('--export-only' in argv, export)
            self.assertEqual(argv[argv.index('--outputs') + 1], str(outputs))

    def test_core_build_receives_semantic_names_and_module_selection(self):
        argv = ['--root', str(self.root), '--receipt-dir', str(self.root / 'receipts'),
                '--rehash', 'Motivic', 'Motivic.Selected']
        with patch('lean_ci.build.build', return_value=7) as build:
            self.assertEqual(module_build.main(argv), 7)
        args, kwargs = build.call_args
        self.assertEqual(args[1], ['Motivic', 'Motivic.Selected'])
        self.assertEqual(kwargs['selection'], 'module')
        self.assertTrue(kwargs['rehash'])

    def test_exact_no_build_export_has_no_miss_fallback(self):
        @contextmanager
        def capped(*args, **kwargs):
            yield dict(os.environ)
        argv = ['--root', str(self.root), '--receipt-dir', str(self.root / 'receipts'),
                '--rehash', '--export-only', '--outputs', str(self.root / 'out.jsonl'), 'Motivic']
        with patch('lean_ci.build.capped_toolchain', capped), \
                patch('lean_ci.resources.limits', return_value={}), \
                patch('lean_ci.resources.run', return_value=3) as run, patch('lean_ci.build.build') as build:
            self.assertEqual(module_build.main(argv), 3)
        build.assert_not_called()
        run.assert_called_once()
        self.assertEqual(run.call_args.args[0], ['lake', '--rehash', '--no-build', 'build',
                                               '+Motivic', '-o', str((self.root / 'out.jsonl').resolve())])

    def test_rendered_selectors_are_rejected_before_shared_tooling_execution(self):
        argv = ['--root', str(self.root), '--receipt-dir', str(self.root / 'receipts'), '+Motivic']
        with patch('lean_ci.build.build') as build, redirect_stderr(io.StringIO()):
            self.assertEqual(module_build.main(argv), 1)
        build.assert_not_called()


if __name__ == '__main__':
    unittest.main()
