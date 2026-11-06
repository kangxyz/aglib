"""Staged restore admission, integrity failures and low-space fallback."""
import errno
import io
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import test_checkpoint

checkpoint = test_checkpoint.checkpoint


class StagedRestoreTests(unittest.TestCase):
    def setUp(self):
        self.probe = test_checkpoint.CheckpointTests()
        self.probe.setUp()
        self.addCleanup(self.probe.doCleanups)

    def assert_no_staging(self):
        self.assertEqual(list(self.probe.root.glob('.checkpoint-stage-*')), [])

    def test_low_bytes_and_low_inodes_use_old_restore(self):
        path = self.probe.write('.lake/build/A.olean', 'archived')
        archive, _ = self.probe.pack('root')
        for bytes_free, inodes_free in ((0, 10000), (1024**4, 0)):
            with self.subTest(bytes_free=bytes_free, inodes_free=inodes_free):
                path.write_text('current')
                fake = SimpleNamespace(f_frsize=4096, f_bavail=bytes_free // 4096,
                                       f_favail=inodes_free)
                with patch.object(checkpoint.os, 'statvfs', return_value=fake), patch.object(
                        checkpoint, 'restore_two_pass', wraps=checkpoint.restore_two_pass) as fallback:
                    self.probe.restore('root', archive)
                    self.assertEqual(fallback.call_count, 1)
                self.assertEqual(path.read_text(), 'archived')
                self.assert_no_staging()

    @unittest.skipUnless(shutil.which('zstd'), 'requires zstd')
    def test_compressed_low_space_falls_back_cleanly(self):
        path = self.probe.write('.lake/build/A.olean', 'archived')
        archive, _ = self.probe.pack('root')
        compressed = archive.with_suffix('.tar.zst')
        compressed.write_bytes(subprocess.check_output(['zstd', '-q', '-c', str(archive)]))
        path.write_text('current')
        fake = SimpleNamespace(f_frsize=4096, f_bavail=0, f_favail=10000)
        with patch.object(checkpoint.os, 'statvfs', return_value=fake), patch.object(
                checkpoint, 'restore_two_pass', wraps=checkpoint.restore_two_pass) as fallback:
            self.probe.restore('root', compressed)
            self.assertEqual(fallback.call_count, 1)
        self.assertEqual(path.read_text(), 'archived')
        self.assert_no_staging()

    def test_fallback_rejects_decoder_error_after_complete_tar_output(self):
        path = self.probe.write('.lake/build/A.olean', 'archived')
        archive, _ = self.probe.pack('root')
        raw_tar = archive.read_bytes()
        compressed = archive.with_suffix('.tar.zst')
        compressed.write_bytes(b'fake compressed input')
        path.write_text('current')
        fake_space = SimpleNamespace(f_frsize=4096, f_bavail=0, f_favail=10000)

        def failed_decoder(*args, **kwargs):
            return SimpleNamespace(stdout=io.BytesIO(raw_tar), wait=lambda: 1)

        with patch.object(checkpoint.os, 'statvfs', return_value=fake_space), patch.object(
                checkpoint.subprocess, 'Popen', side_effect=failed_decoder), patch.object(
                checkpoint, 'restore_two_pass', wraps=checkpoint.restore_two_pass) as fallback:
            self.probe.restore('root', compressed, code=1)
            self.assertEqual(fallback.call_count, 1)
        self.assertEqual(path.read_text(), 'current')
        self.assertFalse((self.probe.root / '.lake/ci-cache/root.json').exists())
        self.assert_no_staging()

    def test_decoder_padding_is_drained_before_normal_exit(self):
        path = self.probe.write('.lake/build/A.olean', 'archived')
        archive, _ = self.probe.pack('root')
        decoded = archive.read_bytes() + bytes(128 * 1024)
        compressed = archive.with_suffix('.tar.zst')
        compressed.write_bytes(b'fake compressed input')
        path.write_text('current')
        state = {'eof': False}

        class PaddingStream(io.BytesIO):
            def read(self, size=-1):
                data = super().read(size)
                if not data:
                    state['eof'] = True
                return data

        decoder = SimpleNamespace(stdout=PaddingStream(decoded),
                                  wait=lambda: 0 if state['eof'] else 1)
        with patch.object(checkpoint.subprocess, 'Popen', return_value=decoder):
            self.probe.restore('root', compressed)
        self.assertTrue(state['eof'])
        self.assertEqual(path.read_text(), 'archived')
        self.assert_no_staging()

    def test_late_payload_failure_leaves_all_old_files_intact(self):
        first = self.probe.write('.lake/build/A.olean', 'archived-a')
        last = self.probe.write('.lake/build/B.olean', 'archived-b')
        archive, _ = self.probe.pack('root')
        def corrupt_last_payload(members):
            members[-1] = (members[-1][0], b'bad-payload')

        self.probe.rewrite(archive, corrupt_last_payload)
        first.write_text('current-a')
        last.write_text('current-b')
        self.probe.restore('root', archive, code=1)
        self.assertEqual(first.read_text(), 'current-a')
        self.assertEqual(last.read_text(), 'current-b')
        self.assert_no_staging()

    def test_staging_write_failure_leaves_all_old_files_intact(self):
        paths = [self.probe.write(f'.lake/build/{name}.olean', 'archived') for name in ('A', 'B')]
        archive, _ = self.probe.pack('root')
        for path in paths:
            path.write_text('current')
        original = Path.open

        def disk_full(path, *args, **kwargs):
            if path.parent.name.startswith('.checkpoint-stage-') and path.name == '1':
                raise OSError(errno.ENOSPC, 'injected full disk')
            return original(path, *args, **kwargs)

        with patch.object(Path, 'open', disk_full):
            self.probe.restore('root', archive, code=1)
        self.assertEqual([path.read_text() for path in paths], ['current', 'current'])
        self.assert_no_staging()

    @unittest.skipUnless(shutil.which('zstd'), 'requires zstd')
    def test_bad_compressed_footer_leaves_outputs_intact(self):
        path = self.probe.write('.lake/build/A.olean', 'archived')
        archive, _ = self.probe.pack('root')
        compressed = archive.with_suffix('.tar.zst')
        result = subprocess.run(['zstd', '-q', '-c', str(archive)], capture_output=True, check=True)
        compressed.write_bytes(result.stdout[:-4])
        path.write_text('current')
        self.probe.restore('root', compressed, code=1)
        self.assertEqual(path.read_text(), 'current')
        self.assert_no_staging()


    def test_cross_mount_publication_uses_same_parent_two_pass_restore(self):
        paths = [self.probe.write(f'.lake/build/{name}.olean', 'archived') for name in ('A', 'B')]
        archive, _ = self.probe.pack('root')
        original = checkpoint.os.replace

        for failing_index in ('0', '1'):
            with self.subTest(failing_index=failing_index):
                for path in paths:
                    path.write_text('current')

                def cross_mount(source, target):
                    source = Path(source)
                    if source.parent.name.startswith('.checkpoint-stage-') and source.name == failing_index:
                        raise OSError(errno.EXDEV, 'injected cross-mount rename')
                    return original(source, target)

                with patch.object(checkpoint.os, 'replace', cross_mount), patch.object(
                        checkpoint, 'restore_two_pass', wraps=checkpoint.restore_two_pass) as fallback:
                    self.probe.restore('root', archive)
                    self.assertEqual(fallback.call_count, 1)
                self.assertEqual([path.read_text() for path in paths], ['archived', 'archived'])
                self.assertTrue((self.probe.root / '.lake/ci-cache/root.json').is_file())
                self.assert_no_staging()

    def test_context_change_during_staging_rejects_before_publication(self):
        path = self.probe.write('.lake/build/A.olean', 'archived')
        archive, _ = self.probe.pack('root')
        path.write_text('current')
        original = checkpoint.file_hash

        def change_context_after_staging(candidate):
            result = original(candidate)
            if candidate == archive:
                self.probe.write('lakefile.toml', 'name="Changed"\n')
            return result

        with patch.object(checkpoint, 'file_hash', change_context_after_staging):
            self.probe.restore('root', archive, code=1)
        self.assertEqual(path.read_text(), 'current')
        self.assert_no_staging()

    def test_low_space_fallback_rejects_corruption_before_overlay(self):
        path = self.probe.write('.lake/build/A.olean', 'archived')
        archive, _ = self.probe.pack('root')

        def corrupt_payload(members):
            members[-1] = (members[-1][0], b'bad-payload')

        self.probe.rewrite(archive, corrupt_payload)
        path.write_text('current')
        fake = SimpleNamespace(f_frsize=4096, f_bavail=0, f_favail=10000)
        with patch.object(checkpoint.os, 'statvfs', return_value=fake), patch.object(
                checkpoint, 'restore_two_pass', wraps=checkpoint.restore_two_pass) as fallback:
            self.probe.restore('root', archive, code=1)
            self.assertEqual(fallback.call_count, 1)
        self.assertEqual(path.read_text(), 'current')
        self.assert_no_staging()

    @unittest.skipUnless(Path('/dev/shm').is_dir() and os.access('/dev/shm', os.W_OK),
                         'requires a writable second Linux filesystem')
    def test_workspace_and_native_outputs_on_different_filesystems(self):
        with tempfile.TemporaryDirectory(prefix='checkpoint-native-', dir='/dev/shm') as directory:
            self.probe.cache = Path(directory)
            if self.probe.cache.stat().st_dev == self.probe.root.stat().st_dev:
                self.skipTest('workspace and native cache share a filesystem')
            dependencies, _ = self.probe.pack('dependencies')
            self.probe.restore('dependencies', dependencies)
            tool = self.probe.write('.lake/lint-runner/BatchedLint.lean', 'generated tool')
            native = self.probe.write('axiom-audit/.lake/build/bin/audit', 'native tool',
                                      root=self.probe.cache)
            archive, _ = self.probe.pack('tools')
            tool.write_text('current')
            native.write_text('current')
            self.probe.restore('tools', archive)
            self.assertEqual(tool.read_text(), 'generated tool')
            self.assertEqual(native.read_text(), 'native tool')
            self.assertEqual(list(self.probe.cache.glob('.checkpoint-stage-*')), [])
            self.assert_no_staging()


if __name__ == '__main__':
    unittest.main()
