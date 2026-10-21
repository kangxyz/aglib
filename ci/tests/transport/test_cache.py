"""Transport/provenance tests with mocked public HTTPS and publication commands."""
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import shutil
import tarfile
import tempfile
import unittest
from unittest.mock import patch
from urllib.error import URLError

from lean_ci.transport import cache


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


    def legacy_coverage(self):
        # Historical core finalizer shape at the supplied source HEAD: no
        # mapping_groups or extracted mappings.py implementation owner.
        return {'schema': 1, 'status': 'complete', 'head': self.revision,
                'plan_id': 'c' * 64, 'required_phases': ['source', 'native'],
                'performed_phases': ['source', 'native'],
                'implementation': {name: 'd' * 64 for name in
                    ('engine.py', 'runtime.py', 'state.py')},
                'performed_checks': [], 'reused_checks': [],
                'compiled_or_refreshed_targets': [], 'reused_build_targets': []}

    def test_historical_asset_with_known_retained_coverage_imports(self):
        payload = archive_bytes(self.provenance, [
            ('validation-coverage.json', json.dumps(self.legacy_coverage()).encode())])
        calls, output, urls = self.restore(lambda *a, **k: io.BytesIO(payload))
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0].args[0][-1], 'Up')
        self.assertEqual(len(urls), 1)
        self.assertIn('imported producer', output)

    def test_historical_known_coverage_is_validated_not_an_arbitrary_extra_allowance(self):
        bad = [b'not-json', b'[]', json.dumps(dict(self.legacy_coverage(), head='b' * 40)).encode(),
               json.dumps(dict(self.legacy_coverage(), status='running')).encode(),
               json.dumps(dict(self.legacy_coverage(), source_basis={'kind': 'working-tree'})).encode()]
        for data in bad:
            with self.subTest(data=data):
                payload = archive_bytes(self.provenance, [('validation-coverage.json', data)])
                with patch.object(cache, 'urlopen', return_value=io.BytesIO(payload)), \
                        patch.object(cache.subprocess, 'run') as run:
                    with self.assertRaises(ValueError):
                        cache.import_candidate(self.root, 'Up', 'Up', 'owner/up', self.revision,
                                               self.revision, 'https://fixture.invalid', self.basis)
                run.assert_not_called()
        payload = archive_bytes(self.provenance, [('other-coverage.json', b'{}')])
        with patch.object(cache, 'urlopen', return_value=io.BytesIO(payload)), \
                patch.object(cache.subprocess, 'run') as run:
            with self.assertRaisesRegex(ValueError, 'unexpected legacy'):
                cache.import_candidate(self.root, 'Up', 'Up', 'owner/up', self.revision,
                                       self.revision, 'https://fixture.invalid', self.basis)
        run.assert_not_called()

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


class MappingGroupTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name).resolve()
        self.root = self.directory / 'repository'
        self.root.mkdir()
        self.client = self.root / 'examples/client'
        self.client.mkdir(parents=True)
        for cwd in (self.root, self.client):
            (cwd / 'lakefile.toml').write_text('name = "Fixture"\n')
        (self.client / 'lakefile.toml').write_text('name = "Client"\n')
        self.mapping = self.directory / 'outputs.jsonl'
        self.coverage = self.mapping.with_suffix('.jsonl.coverage.json')
        self.side = self.mapping.with_name(self.mapping.name + '.groups')
        self.side.mkdir()
        self.paths = [self.mapping, self.side / '0001.jsonl']
        self.revision = 'a' * 40
        for index, path in enumerate(self.paths):
            path.write_text('"2026-03-17"\n' + json.dumps(
                [f'{index:016x}', {'output': f'{index + 1:016x}.olean'}]) + '\n')
        self.summary = {'schema': 1, 'status': 'complete', 'head': self.revision,
                        'plan_id': 'c' * 64, 'required_phases': ['source', 'native'],
                        'performed_phases': ['source', 'native'],
                        'implementation': {name: 'd' * 64 for name in
                            ('engine.py', 'mappings.py', 'runtime.py', 'state.py')},
                        'performed_checks': [], 'reused_checks': [],
                        'compiled_or_refreshed_targets': [], 'reused_build_targets': [],
                        'mapping_groups': []}
        for index, (cwd, path) in enumerate(zip((self.root, self.client), self.paths)):
            self.summary['mapping_groups'].append({
                'path': str(path), 'primary': index == 0, 'sha256': cache.file_hash(path),
                'domain': {'workspace': str(cwd), 'toolchain': {'lean': 'verified'},
                           'platform': [cache.platform.system(), cache.platform.machine()],
                           'format': cache.SUPPORTED_HEADER, 'layout': 'native-lake'}})
        self.save()

    def save(self):
        self.coverage.write_text(json.dumps(self.summary))

    def groups(self):
        with patch.object(cache, 'command', side_effect=lambda cwd, *args:
                          '' if args[1] == 'status' else str(self.root)):
            return cache.mapping_groups(self.root, self.mapping, self.coverage, self.revision)

    def test_complete_groups_retain_separate_producer_workspaces(self):
        self.assertEqual(self.groups(), [(self.root, self.paths[0]), (self.client, self.paths[1])])


    def test_local_and_frozen_head_matches_are_rejected_before_native_stage(self):
        original = json.loads(json.dumps(self.summary))
        for kind in ('working-tree', 'transport-snapshot'):
            with self.subTest(source_basis=kind):
                # Even a local hook that adds HEAD and CI-looking extra fields
                # cannot promote its explicit noncommitted source basis.
                self.summary = dict(original, source_basis={'kind': kind, 'head': self.revision})
                self.save()
                with patch.object(cache, 'command', return_value=self.revision), \
                        patch.object(cache.subprocess, 'run') as run, \
                        patch.object(cache, 'identity') as identity:
                    with self.assertRaisesRegex(ValueError, 'committed CI finalizer envelope'):
                        cache.stage(self.root, self.mapping, self.directory / 'rejected',
                                    'owner/up', self.coverage)
                run.assert_not_called()
                identity.assert_not_called()
        self.summary = original

    def test_missing_or_incomplete_ci_envelopes_are_rejected_before_native_stage(self):
        original = json.loads(json.dumps(self.summary))
        cases = [('plan_id', None), ('plan_id', 'not-a-plan'),
                 ('required_phases', ['native']), ('required_phases', ['source']),
                 ('performed_phases', ['source']), ('performed_phases', ['native', 'source']),
                 ('implementation', {}), ('implementation', {'engine.py': 'unbound'}),
                 ('performed_checks', None)]
        for field, value in cases:
            with self.subTest(field=field, value=value):
                self.summary = dict(original)
                if value is None:
                    self.summary.pop(field)
                else:
                    self.summary[field] = value
                self.save()
                with patch.object(cache, 'command', return_value=self.revision), \
                        patch.object(cache.subprocess, 'run') as run, \
                        patch.object(cache, 'identity') as identity:
                    with self.assertRaisesRegex(ValueError, 'committed CI'):
                        cache.stage(self.root, self.mapping, self.directory / 'rejected',
                                    'owner/up', self.coverage)
                run.assert_not_called()
                identity.assert_not_called()
        self.summary = original

    def test_matching_committed_envelope_rejects_dirty_source_before_native_stage(self):
        def command(cwd, *args):
            if args[1] == 'status':
                return ' M Fixture.lean'
            return self.revision
        with patch.object(cache, 'command', side_effect=command), \
                patch.object(cache.subprocess, 'run') as run, \
                patch.object(cache, 'identity') as identity:
            with self.assertRaisesRegex(ValueError, 'clean HEAD'):
                cache.stage(self.root, self.mapping, self.directory / 'rejected',
                            'owner/up', self.coverage)
        run.assert_not_called()
        identity.assert_not_called()
        self.assertFalse((self.directory / 'rejected').exists())

    def test_source_status_hash_path_and_domain_changes_are_rejected(self):
        cases = [('head', 'b' * 40), ('status', 'running'), ('schema', 2)]
        for field, value in cases:
            with self.subTest(field=field):
                original = self.summary[field]
                self.summary[field] = value
                self.save()
                with self.assertRaises(ValueError):
                    self.groups()
                self.summary[field] = original
        group = self.summary['mapping_groups'][1]
        for field, value in [('path', str(self.directory / 'unexpected.jsonl')),
                             ('sha256', 'f' * 64), ('primary', True)]:
            with self.subTest(field=field):
                original = group[field]
                group[field] = value
                self.save()
                with self.assertRaises(ValueError):
                    self.groups()
                group[field] = original
        domain = group['domain']
        for field, value in [('workspace', str(self.directory)), ('format', 'old'),
                             ('toolchain', {'lean': 'different'}), ('platform', ['other', 'cpu'])]:
            with self.subTest(field=field):
                original = domain[field]
                domain[field] = value
                self.save()
                with self.assertRaises(ValueError):
                    self.groups()
                domain[field] = original

    def test_missing_corrupt_extra_and_symlink_side_files_are_rejected(self):
        side = self.paths[1]
        original = side.read_bytes()
        side.unlink()
        with self.assertRaises((ValueError, OSError)):
            self.groups()
        side.write_bytes(original + b'corrupt')
        with self.assertRaises(ValueError):
            self.groups()
        side.write_bytes(original)
        extra = self.side / '0002.jsonl'
        extra.write_bytes(original)
        with self.assertRaises(ValueError):
            self.groups()
        extra.unlink()
        side.unlink()
        other = self.directory / 'other.jsonl'
        other.write_bytes(original)
        side.symlink_to(other)
        with self.assertRaises(ValueError):
            self.groups()

    def test_conflicting_and_unsafe_native_rows_are_rejected(self):
        for rows in [ [['0' * 16, None], ['0' * 16, True]],
                      [['0' * 16, '../escape']], [['0' * 16, '1' * 16 + '.x/escape']],
                      [['0' * 16, -1]], [['0' * 16, 2 ** 64]], [['0' * 16, 1.5]] ]:
            with self.subTest(rows=rows):
                self.mapping.write_text('"2026-03-17"\n' + ''.join(json.dumps(row) + '\n' for row in rows))
                with self.assertRaises(ValueError):
                    cache.read_mapping(self.mapping)


    def staged(self, *, coverage=True, artifact_data=None):
        destination = self.directory / 'staged'
        basis = {'toolchain': 'fixture', 'compiler': 'fixture', 'system': 'Test', 'arch': 'CPU'}
        calls = []
        def execute(args, **kwargs):
            calls.append((args, kwargs))
            self.assertEqual(args[:3], ['lake', 'cache', 'stage'])
            path, native = Path(args[3]), Path(args[4])
            native.mkdir()
            shutil.copyfile(path, native / 'outputs.jsonl')
            for name in cache.mapping_artifacts(path):
                data = artifact_data(kwargs['cwd'], name) if artifact_data else name.encode()
                (native / name).write_bytes(data)
            return subprocess.CompletedProcess(args, 0)
        def command(cwd, *args):
            if args[1] == 'status':
                return ''
            if args[1] == 'show':
                return (self.root / args[2].split(':', 1)[1]).read_text().strip()
            return str(self.root) if args[-1] == '--show-toplevel' else self.revision
        with patch.object(cache, 'command', side_effect=command), \
                patch.object(cache, 'identity', return_value=basis), \
                patch.object(cache.subprocess, 'run', side_effect=execute), \
                redirect_stdout(io.StringIO()):
            cache.stage(self.root, self.mapping, destination, 'owner/up',
                        self.coverage if coverage else None)
        return destination, calls, basis

    def test_stage_preserves_all_groups_and_uses_each_native_cache_cwd(self):
        # A cross-domain input collision stays isolated in the separate maps.
        self.paths[1].write_text('"2026-03-17"\n' + json.dumps(
            ['0' * 16, {'output': '2' * 16 + '.olean'}]) + '\n')
        self.summary['mapping_groups'][1]['sha256'] = cache.file_hash(self.paths[1])
        self.save()
        destination, calls, _ = self.staged()
        self.assertEqual([kwargs['cwd'] for _, kwargs in calls], [self.root, self.client])
        self.assertTrue(all(args[:3] == ['lake', 'cache', 'stage'] for args, _ in calls))
        self.assertEqual((destination / 'outputs.jsonl').read_bytes(), self.paths[0].read_bytes())
        self.assertEqual((destination / 'outputs.0001.jsonl').read_bytes(), self.paths[1].read_bytes())
        self.assertEqual({path.name for path in destination.iterdir()},
                         {'outputs.jsonl', 'outputs.0001.jsonl', 'provenance.json',
                          'mapping-groups.json', '0000000000000001.olean', '2' * 16 + '.olean'})
        groups = json.loads((destination / 'mapping-groups.json').read_text())['groups']
        self.assertEqual([(group['package'], group['workspace']) for group in groups],
                         [('Fixture', '.'), ('Client', 'examples/client')])
        self.assertEqual(cache.validate_staged_groups(destination, 'Fixture'), 1)

    def test_legacy_stage_remains_one_native_flat_directory(self):
        self.paths[1].unlink()
        self.side.rmdir()
        destination, calls, _ = self.staged(coverage=False)
        self.assertEqual(len(calls), 1)
        self.assertEqual({path.name for path in destination.iterdir()},
                         {'outputs.jsonl', 'provenance.json', '0000000000000001.olean'})
        self.assertEqual(cache.validate_staged_groups(destination, 'Fixture'), 0)


    def test_legacy_single_mapping_does_not_acquire_committed_ci_admission(self):
        self.paths[1].unlink()
        self.side.rmdir()
        with patch.object(cache, 'clean_publication_source', side_effect=AssertionError(
                'Legacy trusted producer does not require the coverage source gate')):
            destination, calls, _ = self.staged(coverage=False)
        self.assertTrue((destination / 'outputs.jsonl').is_file())
        self.assertEqual(len(calls), 1)

    def test_conflicting_artifact_bytes_fail_without_publishing_destination(self):
        self.paths[1].write_bytes(self.paths[0].read_bytes())
        self.summary['mapping_groups'][1]['sha256'] = cache.file_hash(self.paths[1])
        self.save()
        with self.assertRaisesRegex(ValueError, 'Conflicting native staged artifact'):
            self.staged(artifact_data=lambda cwd, name: str(cwd).encode())
        self.assertFalse((self.directory / 'staged').exists())

    def test_corrupt_group_fails_before_any_native_stage(self):
        self.paths[1].write_text('corrupt')
        with patch.object(cache, 'command', return_value=self.revision), \
                patch.object(cache.subprocess, 'run') as run, \
                patch.object(cache, 'identity') as identity:
            with self.assertRaises(ValueError):
                cache.stage(self.root, self.mapping, self.directory / 'staged', 'owner/up', self.coverage)
        run.assert_not_called()
        identity.assert_not_called()

    def test_restore_registers_primary_only_and_reports_retained_clients(self):
        destination, _, basis = self.staged()
        shutil.copyfile(self.coverage, destination / 'validation-coverage.json')
        payload = io.BytesIO()
        with tarfile.open(fileobj=payload, mode='w:gz') as archive:
            for path in destination.iterdir():
                archive.add(path, arcname=path.name)
        observed = []
        def unstage(args, **kwargs):
            self.assertEqual(args[:3], ['lake', 'cache', 'unstage'])
            staged = Path(args[3])
            observed.append((args, (staged / 'outputs.jsonl').read_bytes()))
            self.assertTrue((staged / 'outputs.0001.jsonl').is_file())
            return subprocess.CompletedProcess(args, 0)
        with patch.object(cache, 'urlopen', return_value=io.BytesIO(payload.getvalue())), \
                patch.object(cache.subprocess, 'run', side_effect=unstage), \
                redirect_stdout(io.StringIO()) as output:
            cache.import_candidate(self.root, 'Fixture', 'Fixture', 'owner/up', self.revision,
                                   self.revision, 'https://fixture.invalid', basis)
        self.assertEqual(len(observed), 1)
        self.assertEqual(observed[0][0][-1], 'Fixture')
        self.assertEqual(observed[0][1], self.paths[0].read_bytes())
        self.assertIn('retained 1 client mapping groups; not registered', output.getvalue())


    def test_release_tar_preserves_complete_flat_multi_group_payload(self):
        destination, _, _ = self.staged()
        # Actual Aglib workflow copies this after the cache stage command.
        shutil.copyfile(self.coverage, destination / 'validation-coverage.json')
        expected = {path.name for path in destination.iterdir()}
        uploaded = []
        def execute(args, **kwargs):
            if args[:3] == ['gh', 'run', 'download']:
                shutil.copytree(destination, Path(args[args.index('--dir') + 1]))
            elif args[:3] == ['gh', 'release', 'upload']:
                with tarfile.open(args[4]) as archive:
                    uploaded.append(set(archive.getnames()))
            return subprocess.CompletedProcess(args, 0)
        with patch.dict(os.environ, GITHUB_RUN_ID='123'), \
                patch.object(cache.subprocess, 'run', side_effect=execute), \
                patch.object(cache, 'command', side_effect=subprocess.CalledProcessError(1, ['gh'])):
            cache.release(self.root, 'owner/up', self.revision, 'same-run-artifact')
        self.assertEqual(uploaded, [expected])


    def test_retained_new_coverage_is_hash_bound_and_exact_named(self):
        destination, _, _ = self.staged()
        retained = destination / 'validation-coverage.json'
        shutil.copyfile(self.coverage, retained)
        self.assertEqual(cache.validate_staged_groups(destination, 'Fixture'), 1)
        changed = json.loads(retained.read_text())
        changed['baseline'] = 'e' * 40
        retained.write_text(json.dumps(changed))
        with self.assertRaisesRegex(ValueError, 'differs from staged producer coverage'):
            cache.validate_staged_groups(destination, 'Fixture')
        shutil.copyfile(self.coverage, retained)
        (destination / 'other-coverage.json').write_text('{}')
        with self.assertRaisesRegex(ValueError, 'unexpected staged'):
            cache.validate_staged_groups(destination, 'Fixture')

    def test_removed_metadata_cannot_downgrade_side_maps_to_legacy(self):
        destination, _, _ = self.staged()
        (destination / 'mapping-groups.json').unlink()
        with self.assertRaisesRegex(ValueError, 'unexpected legacy'):
            cache.validate_staged_groups(destination, 'Fixture')

    def test_staged_metadata_rejects_package_scope_tampering_and_extra_files(self):
        destination, _, _ = self.staged()
        with self.assertRaisesRegex(ValueError, 'package'):
            cache.validate_staged_groups(destination, 'Client')
        extra = destination / 'outputs.0002.jsonl'
        extra.write_bytes(self.paths[1].read_bytes())
        with self.assertRaisesRegex(ValueError, 'unexpected'):
            cache.validate_staged_groups(destination, 'Fixture')

    def test_single_mapping_cannot_silently_drop_side_groups(self):
        with self.assertRaises(ValueError):
            cache.mapping_groups(self.root, self.mapping, None, self.revision)
        self.paths[1].unlink()
        self.side.rmdir()
        self.assertEqual(cache.mapping_groups(self.root, self.mapping, None, self.revision),
                         [(self.root, self.mapping)])


if __name__ == '__main__':
    unittest.main()
