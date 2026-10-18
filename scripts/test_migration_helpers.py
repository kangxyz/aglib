"""Bounded regression checks for retired extraction writers and guarded inspection."""
import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import migration_helpers as helpers

REVISION = '189a8e779f0c68b2dfc6f8195daebb3e684a5905'


class MigrationHelperTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='aglib-source-inspection-')
        self.root = Path(self.tmp.name)
        self.source = self.root / 'Quillen/Example.lean'
        self.source.parent.mkdir()
        self.original = b'/- Original source identity. -/\r\nmodule\r\n'
        self.source.write_bytes(self.original)
        self.sha256 = hashlib.sha256(self.original).hexdigest()

    def tearDown(self):
        self.tmp.cleanup()

    def inspect(self, revision=REVISION, sha256=None):
        with patch('migration_helpers.subprocess.run', return_value=
                   subprocess.CompletedProcess([], 0, REVISION + '\n', '')):
            return helpers.read_source('Quillen.Example', source_root=self.root,
                expected_revision=revision, expected_sha256=sha256 or self.sha256)

    def test_source_root_is_explicit_and_original_bytes_are_identified(self):
        with self.assertRaises(TypeError):
            helpers.source_path('Quillen.Example')
        text, metadata = self.inspect()
        self.assertEqual(text.encode('utf-8'), self.original)
        self.assertEqual(metadata, {'source_module': 'Quillen.Example',
            'source_repository': 'quillen-k-theory', 'source_revision': REVISION,
            'source_sha256': self.sha256})
        self.assertEqual(self.source.read_bytes(), self.original)

    def test_revision_and_hash_mismatch_fail_before_returning_source(self):
        with self.assertRaisesRegex(ValueError, 'revision does not match'):
            self.inspect(revision='0' * 40)
        with self.assertRaisesRegex(ValueError, 'bytes do not match'):
            self.inspect(sha256='0' * 64)
        self.assertEqual(self.source.read_bytes(), self.original)

    def test_missing_identity_and_source_escape_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'exact Git revision'):
            self.inspect(revision='189a8e7')
        with self.assertRaises(ValueError):
            helpers.source_path('Quillen.../outside', source_root=self.root)

    def test_retired_writers_cannot_overwrite_redesigned_files_or_provenance(self):
        destination = self.root / 'Aglib/Example.lean'
        destination.parent.mkdir()
        destination.write_text('maintained redesigned source\n')
        provenance = self.root / 'docs/migration/example.json'
        provenance.parent.mkdir(parents=True)
        provenance.write_text('{"source_revision":"immutable"}\n')
        before = {path: path.read_bytes() for path in [destination, provenance]}
        with patch.object(helpers, 'ROOT', self.root), \
                patch.object(helpers, 'source_path', side_effect=AssertionError('must not read source')):
            with self.assertRaisesRegex(RuntimeError, 'writing is retired'):
                helpers.write_source('Quillen.Example', destination='Aglib.Example')
            with self.assertRaisesRegex(RuntimeError, 'recording is retired'):
                helpers.record('example', [])
        self.assertEqual({path: path.read_bytes() for path in before}, before)


if __name__ == '__main__':
    unittest.main()
