"""Fixed native fixture source admission and copying; no Lean is launched."""
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import native_test as fixture


class FixedFixtureTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='lean-ci-fixed-fixture-')
        self.addCleanup(self.temporary.cleanup)
        self.scratch = Path(self.temporary.name)
        self.root = self.scratch / 'fixture'

    def test_fixture_copies_reviewed_lean_sources_byte_for_byte(self):
        fixture.create_fixture(self.root, 'fixture-pinned-toolchain')
        for target, source in {'Quartz.lean': 'Quartz.lean', 'Check.lean': 'Check.lean',
                               'Quartz/Upstream.lean': 'upstream7.lean',
                               'lakefile.toml': 'lakefile.toml'}.items():
            self.assertEqual((self.root / target).read_bytes(),
                             (fixture.FIXTURE_DIRECTORY / source).read_bytes())
        self.assertEqual(fixture.git(self.root, 'status', '--porcelain'), '')

    def test_upstream_transition_copies_only_the_reviewed_alternate_source(self):
        fixture.create_fixture(self.root, 'fixture-pinned-toolchain')
        unchanged = {name: (self.root / name).read_bytes()
                     for name in ('Quartz.lean', 'Check.lean', 'lakefile.toml')}
        fixture.change_upstream(self.root)
        self.assertEqual(fixture.git(self.root, 'diff', '--name-only', 'HEAD^', 'HEAD'),
                         'Quartz/Upstream.lean')
        self.assertEqual((self.root / 'Quartz/Upstream.lean').read_bytes(),
                         (fixture.FIXTURE_DIRECTORY / 'upstream9.lean').read_bytes())
        self.assertTrue(all((self.root / name).read_bytes() == source
                            for name, source in unchanged.items()))

    def test_changed_fixture_source_is_rejected_before_git_or_native_work(self):
        catalog = self.scratch / 'catalog'
        shutil.copytree(fixture.FIXTURE_DIRECTORY, catalog)
        (catalog / 'Check.lean').write_text('example : True := trivial\n')
        with patch.object(fixture, 'FIXTURE_DIRECTORY', catalog), \
                patch.object(fixture, 'git') as git:
            with self.assertRaisesRegex(ValueError, 'Unreviewed native fixture source'):
                fixture.create_fixture(self.root, 'fixture-pinned-toolchain')
            git.assert_not_called()


if __name__ == '__main__':
    unittest.main()
