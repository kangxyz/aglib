"""Transport validation and selective derived-only repair; no proof replay."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('native_stage', Path(__file__).with_name('stage.py'))
stage = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(stage)


class StageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name).resolve()
        self.root = self.base / 'root'; self.root.mkdir()
        self.native = self.base / 'native'; self.native.mkdir()
        self.payload = self.base / 'stage'; self.payload.mkdir()
        self.name = 'a' * 16 + '.ltar'
        self.mapping = self.payload / 'outputs.jsonl'
        self.mapping.write_text(json.dumps(stage.MAP_SCHEMA) + '\n' +
                                json.dumps(['b' * 16, self.name]) + '\n')
        (self.payload / self.name).write_bytes(b'bad archive bytes')

    def test_native_map_rejects_unknown_or_escaping_descriptors(self):
        self.assertEqual(stage.read_map(self.mapping), {self.name: 'b' * 16})
        for content in ('"unknown"\n', json.dumps(stage.MAP_SCHEMA) + '\n' +
                        json.dumps(['b' * 16, '../outside.ltar']) + '\n'):
            self.mapping.write_text(content)
            with self.assertRaises(ValueError):
                stage.read_map(self.mapping)

    def test_validator_deletes_only_disposable_copies_for_confirmed_corruption(self):
        name = self.name
        class CorruptRunner:
            def run(self, argv, *, stdin, **_):
                row = json.loads(stdin)[0]
                copy = Path(row['file'])
                copy.unlink()
                return 0, str(copy) + ': removing corrupted file\n'
        result = stage.validate(self.payload, 'leantar', CorruptRunner(), self.base / 'scratch')
        self.assertEqual(result['bad_archives'], [name])
        self.assertTrue((self.payload / name).is_file())

    def test_io_error_never_authorizes_archive_invalidation(self):
        class IOErrorRunner:
            def run(self, argv, *, stdin, **_):
                copy = Path(json.loads(stdin)[0]['file'])
                copy.unlink()
                return 1, str(copy) + ': No space left on device\n'
        with self.assertRaisesRegex(ValueError, 'non-corruption/IO'):
            stage.validate(self.payload, 'leantar', IOErrorRunner(), self.base / 'scratch')
        self.assertTrue((self.payload / self.name).is_file())

    def test_invalid_magic_is_reported_even_when_leantar_does_not_delete_copy(self):
        class MagicRunner:
            def run(self, argv, *, stdin, **_):
                copy = Path(json.loads(stdin)[0]['file'])
                return 1, str(copy) + ': bad .ltar file\n'
        result = stage.validate(self.payload, 'leantar', MagicRunner(), self.base / 'scratch')
        self.assertEqual(result['bad_archives'], [self.name])
        self.assertTrue((self.payload / self.name).is_file())

    def test_selective_invalidation_preserves_compiled_bytes_and_other_archives(self):
        ir = self.root / '.lake/build/ir'; ir.mkdir(parents=True)
        bad = ir / 'Bad.ltar'; bad.write_bytes((self.payload / self.name).read_bytes())
        Path(str(bad) + '.hash').write_text('old hash')
        good = ir / 'Good.ltar'; good.write_bytes(b'good archive bytes')
        olean = self.root / '.lake/build/lib/lean/Bad.olean'
        olean.parent.mkdir(parents=True); olean.write_bytes(b'valid compiled proof data')
        artifact = self.native / 'artifacts' / self.name
        artifact.parent.mkdir(); artifact.write_bytes(bad.read_bytes())
        removed, hashes = stage.invalidate(self.root, self.native, self.payload, [self.name])
        self.assertEqual(len(removed), 3)
        self.assertTrue(good.exists())
        self.assertEqual(olean.read_bytes(), b'valid compiled proof data')
        self.assertEqual(hashes[str(olean)], stage.sha(olean))
        self.assertFalse(bad.exists())

    def test_metadata_guard_rejects_frontend(self):
        env = stage.metadata_guard(sys.executable, self.base)
        result = subprocess.run([env['LEAN'], 'Proof.lean'], env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(result.returncode, 94)

    def test_deadline_terminates_and_waits_owned_group(self):
        runner = stage.Runner(self.root, seconds=.1)
        with self.assertRaises(subprocess.TimeoutExpired):
            runner.run([sys.executable, '-c', 'import time; time.sleep(60)'])


if __name__ == '__main__':
    unittest.main()
