"""Transport/provenance tests with mocked public HTTPS and publication commands."""
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch
from urllib.error import URLError

import cache


def archive_bytes(provenance, extra=None):
    result = io.BytesIO()
    with tarfile.open(fileobj=result, mode='w:gz') as archive:
        for name, data in [('provenance.json', json.dumps(provenance).encode()),
                           ('outputs.jsonl', b'"2026-03-17"\n'), *(extra or [])]:
            member = tarfile.TarInfo(name)
            member.size = len(data)
            archive.addfile(member, io.BytesIO(data))
    return result.getvalue()


class TransportTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.revision = 'a' * 40
        self.producer = 'b' * 40
        self.package = {'name': 'Up', 'url': 'https://github.com/owner/up.git',
                        'rev': self.revision, 'type': 'git', 'inherited': False}
        (self.root / 'lake-manifest.json').write_text(json.dumps({'packages': [self.package]}))
        self.basis = dict(toolchain='leanprover/lean4:v4.34.1', compiler='Lean fixture',
                          system='Linux', arch='x86_64')
        self.provenance = dict(self.basis, package='Up', repository='owner/up', revision=self.revision)
        self.seed = dict(tag_name='cache-' + self.producer, draft=False, prerelease=True,
                         target_commitish=self.producer,
                         assets=[dict(name=cache.asset_name(self.basis, self.producer))])

    def restore(self, fetch):
        with patch.object(cache, 'identity', return_value=self.basis), \
                patch.object(cache, 'urlopen', side_effect=fetch) as urls, \
                patch.object(cache.subprocess, 'run') as commands, \
                redirect_stdout(io.StringIO()) as output:
            cache.restore(self.root, ['owner/up'])
        return commands.call_args_list, output.getvalue(), urls.call_args_list

    def test_only_allowlisted_direct_git_dependencies(self):
        variants = [self.package, dict(self.package, name='Inherited', inherited=True),
                    dict(self.package, name='Foreign', url='https://github.com/other/up.git'),
                    dict(self.package, name='Path', type='path')]
        (self.root / 'lake-manifest.json').write_text(json.dumps({'packages': variants}))
        self.assertEqual(list(cache.dependencies(self.root, {'owner/up'})),
                         [('Up', 'Up', 'owner/up', self.revision)])
        self.assertEqual(list(cache.dependencies(self.root, set())), [])

    def test_escaped_hyphenated_identity_retains_native_selector(self):
        self.package['name'] = '«fixture-up»'
        (self.root / 'lake-manifest.json').write_text(json.dumps({'packages': [self.package]}))
        self.provenance['package'] = 'fixture-up'
        self.assertEqual(list(cache.dependencies(self.root, {'owner/up'})),
                         [('fixture-up', '«fixture-up»', 'owner/up', self.revision)])
        calls, output, _ = self.restore(lambda *a, **k: io.BytesIO(archive_bytes(self.provenance)))
        self.assertEqual(calls[0].args[0][-1], '«fixture-up»')
        self.assertIn('fixture-up: imported producer', output)
        for exact in ['«λ-lib»', '«a.b»', '««a-b»»', 'λ-lib']:
            self.assertEqual(cache.package_identity(exact), exact)

    def test_exact_artifact_imports_without_api_or_credentials(self):
        calls, output, urls = self.restore(lambda *a, **k: io.BytesIO(archive_bytes(self.provenance)))
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0].args[0][:3], ['lake', 'cache', 'unstage'])
        self.assertEqual(calls[0].args[0][-1], 'Up')
        self.assertEqual(len(urls), 1)
        self.assertTrue(urls[0].args[0].startswith('https://github.com/owner/up/releases/download/cache-'))
        self.assertIn('imported producer ' + self.revision, output)

    def test_recent_seed_keeps_honest_producer_revision_and_consumer_pin(self):
        def fetch(url, **kwargs):
            if 'api.github.com' in url:
                return io.BytesIO(json.dumps([self.seed]).encode())
            if 'cache-' + self.revision in url:
                raise URLError('not yet built')
            return io.BytesIO(archive_bytes(dict(self.provenance, revision=self.producer)))
        calls, output, urls = self.restore(fetch)
        self.assertEqual(len(calls), 1)
        self.assertEqual(len(urls), 3)
        self.assertIn('producer ' + self.producer + ' for configured pin ' + self.revision, output)

    def test_provenance_mismatch_never_unstages_even_at_same_git_revision(self):
        for field, value in [('compiler', 'another compiler'), ('arch', 'arm64'),
                             ('toolchain', 'another toolchain'), ('package', 'Foreign'),
                             ('repository', 'fork/up'), ('revision', self.producer)]:
            def fetch(url, **kwargs):
                if 'api.github.com' in url:
                    return io.BytesIO(b'[]')
                return io.BytesIO(archive_bytes(dict(self.provenance, **{field: value})))
            calls, output, _ = self.restore(fetch)
            self.assertEqual(calls, [], field)
            self.assertIn('incompatible producer artifact provenance', output)
            self.assertIn('ordinary build fallback', output)

    def test_remote_errors_are_explicit_cache_misses(self):
        def missing(*args, **kwargs):
            raise URLError('not found')
        calls, output, _ = self.restore(missing)
        self.assertEqual(calls, [])
        self.assertIn('ordinary build fallback', output)

    def test_recent_lookup_is_bounded_and_filters_release_identity(self):
        bad = [dict(self.seed, draft=True), dict(self.seed, prerelease=False),
               dict(self.seed, tag_name='v1.0'), dict(self.seed, target_commitish='main'),
               dict(self.seed, assets=[dict(name='incompatible-platform.tar.gz')])]
        records = bad + [dict(self.seed, tag_name='cache-' + f'{n:040x}', target_commitish=f'{n:040x}',
                             assets=[dict(name=cache.asset_name(self.basis, f'{n:040x}'))]) for n in range(30)]
        with patch.object(cache, 'urlopen', return_value=io.BytesIO(json.dumps(records).encode())):
            candidates = cache.recent_candidates('owner/up', self.basis, self.revision)
        self.assertEqual(len(candidates), 5)
        self.assertTrue(all(revision != self.producer for revision, _ in candidates))

    def test_archive_traversal_and_duplicate_entries_are_rejected(self):
        for extra in [[('../escape', b'bad')], [('outputs.jsonl', b'duplicate')]]:
            with self.subTest(extra=extra):
                archive = self.root / 'bad.tar.gz'
                archive.write_bytes(archive_bytes(self.provenance, extra))
                with tempfile.TemporaryDirectory() as destination:
                    with self.assertRaises((ValueError, FileExistsError)):
                        cache.unpack(archive, Path(destination))
        self.assertFalse((self.root.parent / 'escape').exists())

    def test_release_uses_native_files_without_overwriting_existing_asset(self):
        def download(args, **kwargs):
            self.assertEqual(args[:3], ['gh', 'run', 'download'])
            destination = Path(args[args.index('--dir') + 1])
            destination.mkdir()
            (destination / 'provenance.json').write_text(json.dumps(self.provenance))
            (destination / 'outputs.jsonl').write_text('native mappings')
            return subprocess.CompletedProcess(args, 0)
        with patch.dict(os.environ, GITHUB_RUN_ID='123'), \
                patch.object(cache.subprocess, 'run', side_effect=download) as run, \
                patch.object(cache, 'command', return_value=cache.asset_name(self.basis, self.revision)), \
                redirect_stdout(io.StringIO()) as output:
            cache.release(self.root, 'owner/up', self.revision, 'same-run-artifact')
        self.assertEqual(run.call_count, 1)
        self.assertIn('immutable cache asset already exists', output.getvalue())

    def test_new_release_is_prerelease_not_latest_and_never_clobbers(self):
        def execute(args, **kwargs):
            if args[:3] == ['gh', 'run', 'download']:
                destination = Path(args[args.index('--dir') + 1])
                destination.mkdir()
                (destination / 'provenance.json').write_text(json.dumps(self.provenance))
                (destination / 'outputs.jsonl').write_text('native mappings')
            if args[:3] == ['gh', 'release', 'upload']:
                with tarfile.open(args[4]) as archive:
                    self.assertEqual(set(archive.getnames()), {'provenance.json', 'outputs.jsonl'})
            return subprocess.CompletedProcess(args, 0)
        with patch.dict(os.environ, GITHUB_RUN_ID='123'), \
                patch.object(cache.subprocess, 'run', side_effect=execute) as run, \
                patch.object(cache, 'command', side_effect=subprocess.CalledProcessError(1, ['gh'])):
            cache.release(self.root, 'owner/up', self.revision, 'same-run-artifact')
        create = run.call_args_list[1].args[0]
        self.assertIn('--prerelease', create)
        self.assertIn('--latest=false', create)
        self.assertEqual(create[create.index('--target') + 1], self.revision)
        self.assertNotIn('--clobber', run.call_args_list[2].args[0])


if __name__ == '__main__':
    unittest.main()
