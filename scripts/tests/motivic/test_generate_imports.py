# Authors: kangxyz
"""Isolated opt-in facade fixtures; no Lean, dependency cache or Git writes."""
import io
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from lean_tools.motivic.repository import check_repository
from lean_tools.motivic.imports import (GENERATED_MARKER, check_generated, generated_files,
                              generator_owned, main, stale_files, write_generated)
from lean_tools.motivic.sources import is_import_surface, lean_imports, uses_module_system


class FacadeGenerationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.curated = {
            'Motivic.lean': 'module\n\n' + ''.join(
                f'public import Motivic.Core{i}\n' for i in range(4)),
            'MotivicTest.lean': 'module\n\npublic import MotivicTest.First\n'
                                'public import MotivicTest.Second\n',
        }
        for name, content in self.curated.items():
            self.write(name, content)
        for i in range(4):
            self.write(f'Motivic/Core{i}.lean', 'module\n')
        for name in ('First', 'Second'):
            self.write(f'MotivicTest/{name}.lean', 'module\n')

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        return path

    def topic(self):
        self.write('Motivic/Topic.lean', GENERATED_MARKER + 'module\n')
        self.write('Motivic/Topic/Zebra.lean', 'module\n')
        self.write('Motivic/Topic/Nested/Alpha.lean', 'module\n')

    def refresh(self):
        outputs = generated_files(self.root)
        write_generated(self.root, outputs)
        return outputs

    def test_only_exact_initial_marker_transfers_ownership(self):
        header = '/-\nCopyright (c) 2026 Example.\nAuthors: Example Author\n-/\n\n'
        self.assertTrue(generator_owned(GENERATED_MARKER + 'module\n'))
        self.assertTrue(generator_owned(header + GENERATED_MARKER + 'module\n'))
        for source in ('/-!\n' + GENERATED_MARKER + '-/\nmodule\n',
                       'module\n' + GENERATED_MARKER,
                       'def text := "' + GENERATED_MARKER + '"\n',
                       '-- ' + GENERATED_MARKER,
                       ' ' + GENERATED_MARKER,
                       '/-\nCopyright (c) unfinished\n' + GENERATED_MARKER):
            with self.subTest(source=source):
                self.assertFalse(generator_owned(source))
        self.topic()
        self.write('Motivic/Topic.lean', header + GENERATED_MARKER + 'module\n')
        content = self.refresh()[Path('Motivic/Topic.lean')]
        self.assertTrue(content.startswith(header + GENERATED_MARKER))

    def test_actual_family_is_sorted_modern_and_tracks_add_remove(self):
        self.topic()
        self.write('Motivic/Other/AbsentFacade.lean', 'module\n')
        self.write('Motivic/Topic/Manual.lean', 'module\n\ndef value := 1\n')
        outputs = self.refresh()
        self.assertEqual(set(outputs), {Path('Motivic/Topic.lean')})
        content = outputs[Path('Motivic/Topic.lean')]
        self.assertTrue(uses_module_system(content))
        self.assertTrue(is_import_surface(content))
        self.assertEqual(content.count('set_option linter.style.longFile 0'), 1)
        self.assertEqual(lean_imports(content), ['Motivic.Topic.Manual',
                         'Motivic.Topic.Nested.Alpha', 'Motivic.Topic.Zebra'])
        self.assertEqual(stale_files(self.root), [])
        self.write('Motivic/Topic/Added.lean', 'module\n')
        (self.root / 'Motivic/Topic/Zebra.lean').unlink()
        self.assertEqual(stale_files(self.root), [Path('Motivic/Topic.lean')])
        self.refresh()
        grown = (self.root / 'Motivic/Topic.lean').read_text()
        self.assertEqual(lean_imports(grown),
                         ['Motivic.Topic.Added', 'Motivic.Topic.Manual', 'Motivic.Topic.Nested.Alpha'])
        self.assertEqual(grown.count('set_option linter.style.longFile 0'), 1)
        self.assertEqual(stale_files(self.root), [])
        for name, content in self.curated.items():
            self.assertEqual((self.root / name).read_text(), content)

    def test_no_implicit_facade_or_manual_takeover_or_curated_root_expansion(self):
        self.topic()
        manual = 'module\n\npublic import Motivic.Manual.Child\n'
        self.write('Motivic/Manual.lean', manual)
        self.write('Motivic/Manual/Child.lean', 'module\n')
        quoted = '/-!\n' + GENERATED_MARKER + '-/\nmodule\n'
        self.write('Motivic/Quoted.lean', quoted)
        self.write('Motivic/Quoted/Child.lean', 'module\n')
        self.write('Motivic/Implicit/Child.lean', 'module\n')
        self.refresh()
        self.assertEqual((self.root / 'Motivic/Manual.lean').read_text(), manual)
        self.assertEqual((self.root / 'Motivic/Quoted.lean').read_text(), quoted)
        self.assertFalse((self.root / 'Motivic/Implicit.lean').exists())
        for name, content in self.curated.items():
            self.assertEqual((self.root / name).read_text(), content)
            # Even an accidental marker cannot enroll a package root.
            self.write(name, GENERATED_MARKER + content)
        self.assertEqual(set(self.refresh()), {Path('Motivic/Topic.lean')})
        for name, content in self.curated.items():
            self.assertEqual((self.root / name).read_text(), GENERATED_MARKER + content)

    def test_marked_implementation_and_unoccupied_facade_are_rejected(self):
        self.topic()
        implementation = GENERATED_MARKER + 'module\n\ndef value := 1\n'
        self.write('Motivic/Topic.lean', implementation)
        with self.assertRaisesRegex(ValueError, 'contains implementation'):
            self.refresh()
        self.assertEqual((self.root / 'Motivic/Topic.lean').read_text(), implementation)
        self.write('Motivic/Topic.lean', GENERATED_MARKER + 'module\n')
        self.write('Motivic/Empty.lean', GENERATED_MARKER + 'module\n')
        (self.root / 'Motivic/Empty').mkdir()
        with self.assertRaisesRegex(ValueError, 'occupied same-named directory'):
            self.refresh()

    def test_legacy_child_is_not_silently_enrolled_in_modern_facade(self):
        self.topic()
        self.write('Motivic/Topic/Legacy.lean', 'import Mathlib\n')
        with self.assertRaisesRegex(ValueError, 'legacy child sources'):
            self.refresh()

    def test_nested_opt_in_facades_are_generated_together(self):
        self.topic()
        self.write('Motivic/Topic/Nested.lean', GENERATED_MARKER + 'module\n')
        outputs = self.refresh()
        self.assertEqual(set(outputs), {Path('Motivic/Topic.lean'), Path('Motivic/Topic/Nested.lean')})
        self.assertIn('Motivic.Topic.Nested', lean_imports(outputs[Path('Motivic/Topic.lean')]))
        self.assertEqual(lean_imports(outputs[Path('Motivic/Topic/Nested.lean')]),
                         ['Motivic.Topic.Nested.Alpha'])

    def test_direct_and_indirect_implementation_cycles_fail_before_any_cli_write(self):
        for imported, bridge in [('Motivic.Topic', None), ('Motivic.Bridge', 'Motivic.Topic')]:
            with self.subTest(imported=imported):
                self.topic()
                self.write('Motivic/Topic/Zebra.lean', f'module\npublic import {imported}\n')
                if bridge:
                    self.write('Motivic/Bridge.lean', f'module\npublic import {bridge}\n')
                self.write('Motivic/Another.lean', GENERATED_MARKER + 'module\n')
                self.write('Motivic/Another/Leaf.lean', 'module\n')
                before = {path: path.read_bytes() for path in self.root.rglob('*.lean')}
                with patch.object(sys, 'argv', ['generate_imports.py', '--root', str(self.root)]), \
                        redirect_stderr(io.StringIO()) as errors:
                    self.assertEqual(main(), 1)
                self.assertIn('Generated facade import cycle:', errors.getvalue())
                self.assertEqual({path: path.read_bytes() for path in self.root.rglob('*.lean')}, before)

    def test_new_edges_between_two_facades_are_checked_together(self):
        self.topic()
        self.write('Motivic/Other.lean', GENERATED_MARKER + 'module\n')
        self.write('Motivic/Other/Leaf.lean', 'module\npublic import Motivic.Topic\n')
        self.write('Motivic/Topic/Zebra.lean', 'module\npublic import Motivic.Other\n')
        with self.assertRaisesRegex(ValueError, 'Generated facade import cycle'):
            generated_files(self.root)

    def test_write_rechecks_manual_ownership_before_any_output(self):
        self.topic()
        outputs = generated_files(self.root)
        manual = 'module\n\npublic import Motivic.Topic.Zebra\n'
        self.write('Motivic/Topic.lean', manual)
        with self.assertRaisesRegex(ValueError, 'inputs changed'):
            write_generated(self.root, outputs)
        self.assertEqual((self.root / 'Motivic/Topic.lean').read_text(), manual)

    def test_check_mode_and_repository_enrollment_report_stale_without_writes(self):
        self.topic()
        before = (self.root / 'Motivic/Topic.lean').read_bytes()
        with patch.object(sys, 'argv', ['generate_imports.py', '--root', str(self.root), '--check']), \
                redirect_stderr(io.StringIO()) as errors:
            self.assertEqual(main(), 1)
        self.assertIn('Stale generated facades', errors.getvalue())
        self.assertEqual((self.root / 'Motivic/Topic.lean').read_bytes(), before)
        self.assertTrue(any('Stale generated facades' in error
                            for error in check_repository(self.root)[0]))
        self.refresh()
        self.assertEqual(check_generated(self.root), [])
        with patch.object(sys, 'argv', ['generate_imports.py', '--root', str(self.root), '--check']), \
                redirect_stdout(io.StringIO()):
            self.assertEqual(main(), 0)


if __name__ == '__main__':
    unittest.main()
