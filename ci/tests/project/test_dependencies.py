"""Pinned old/current source evidence and explicit source-only acquisition."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from lean_ci.project.dependencies import (DependencySourcesUnavailable, affected_origins,
                                          resolve_planning_sources)
from lean_ci.project import dependencies


class DependenciesTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name).resolve()
        self.root = self.directory / 'project'
        self.root.mkdir()
        self.git(self.root, 'init', '-q')
        self.workspace = {'id': 'root', 'path': '.', 'package': 'Tiny'}
        self.client = {'id': 'client', 'path': 'examples/client', 'package': 'Client'}
        self.config = {'package_dir': '.', 'config_path': '.github/lean-ci.toml',
                       'workspaces': [self.workspace, self.client]}
        self.a = self.repo('a', {'lakefile.toml': 'name="Aglib"\n[[lean_lib]]\nname="Aglib"\n',
                                 'Aglib/Provider.lean': 'import Mathlib.X\n'})
        self.a_pin = self.pin('Aglib', self.a)
        self.b = self.repo('b', {'lakefile.toml': 'name="mathlib"\n[[lean_lib]]\nname="Mathlib"\n',
                                 'Mathlib/X.lean': 'import Init\ndef x := 1\n'})
        self.old_b = self.pin('mathlib', self.b)
        (self.b / 'Mathlib/X.lean').write_text('import Init\ndef x := 2\n')
        self.commit(self.b)
        self.new_b = self.pin('mathlib', self.b)
        self.old_pins = {'Aglib': self.a_pin, 'mathlib': self.old_b}
        self.new_pins = {'Aglib': self.a_pin, 'mathlib': self.new_b}
        self.old = self.records()
        self.current = self.records()
        self.write_manifest(self.old_pins)
        self.base = self.commit(self.root)
        self.write_manifest(self.new_pins)

    def git(self, cwd, *args):
        result = subprocess.run(['git', *args], cwd=cwd, capture_output=True, text=True,
                                env=dict(os.environ, GIT_CONFIG_NOSYSTEM='1', GIT_NO_REPLACE_OBJECTS='1'))
        if result.returncode:
            raise AssertionError(result.stderr)
        return result.stdout.strip()

    def commit(self, directory):
        self.git(directory, 'add', '.')
        self.git(directory, '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 '-c', 'commit.gpgsign=false', 'commit', '-qm', 'fixture')
        return self.git(directory, 'rev-parse', 'HEAD')

    def repo(self, name, files):
        directory = self.directory / name
        directory.mkdir()
        self.git(directory, 'init', '-q')
        for path, text in files.items():
            target = directory / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
        self.commit(directory)
        return directory

    def pin(self, name, repository):
        return {'name': name, 'type': 'git', 'url': str(repository),
                'rev': self.git(repository, 'rev-parse', 'HEAD'), 'subDir': None}

    def write_manifest(self, pins):
        (self.root / 'lake-manifest.json').write_text(json.dumps({'name': 'Tiny', 'packages': list(pins.values())}))

    def records(self):
        return {
            'Tiny.Provider': {'workspace': 'root', 'imports': ['Aglib.Provider']},
            'Tiny.Consumer': {'workspace': 'root', 'imports': ['Tiny.Provider']},
            'TinyTest.Positive': {'workspace': 'root', 'imports': ['Tiny.Consumer']},
            'Tiny.Unrelated': {'workspace': 'root', 'imports': ['Init']},
            'client:Client.Indirect': {'workspace': 'client', 'imports': ['Tiny.Consumer']},
            'client:Client.Direct': {'workspace': 'client', 'imports': ['Mathlib.X']},
        }

    def acquire(self, **kwargs):
        return resolve_planning_sources(self.root, self.config, self.base,
                                         workspace=self.workspace, allow_local=True, **kwargs)

    def affected(self, changed=('mathlib',), **kwargs):
        return affected_origins(self.root, self.config, self.workspace, self.base,
                                self.current, self.old, changed,
                                kwargs.get('old_pins', self.old_pins), kwargs.get('new_pins', self.new_pins))

    def test_cold_typed_gap_then_source_only_acquisition_reaches_narrow_closure(self):
        with self.assertRaises(DependencySourcesUnavailable):
            self.affected()
        result = self.acquire()
        self.assertEqual(result['status'], 'sources-ready')
        self.assertEqual(self.affected(), set(self.current) - {'Tiny.Unrelated'})
        self.assertEqual(self.git(self.root / '.lake/packages/mathlib', 'rev-parse', 'HEAD'), self.new_b['rev'])
        self.assertFalse((self.root / '.lake/build').exists())
        self.assertEqual({p['revision'] for p in result['fetched']},
                         {self.a_pin['rev'], self.old_b['rev'], self.new_b['rev']})

    def test_old_removed_dependency_module_owner_and_removed_local_key_survive(self):
        self.acquire()
        (self.b / 'Mathlib/X.lean').unlink()
        (self.b / 'Renamed').mkdir()
        (self.b / 'Renamed/Y.lean').write_text('import Init\n')
        self.commit(self.b)
        new = self.pin('mathlib', self.b)
        self.write_manifest({'Aglib': self.a_pin, 'mathlib': new})
        self.current = {'Tiny.Unrelated': self.current['Tiny.Unrelated'],
                        'TinyTest.Positive': {'workspace': 'root', 'imports': ['Init']}}
        self.acquire()
        result = self.affected(new_pins={'Aglib': self.a_pin, 'mathlib': new})
        self.assertIn('Tiny.Provider', result)
        self.assertIn('TinyTest.Positive', result)
        self.assertNotIn('Tiny.Unrelated', result)

    def test_current_stale_import_of_removed_old_provider_is_still_selected(self):
        self.acquire()
        (self.b / 'Mathlib/X.lean').unlink()
        (self.b / 'Mathlib/New.lean').write_text('import Init\n')
        self.commit(self.b)
        latest = self.pin('mathlib', self.b)
        self.write_manifest({'Aglib': self.a_pin, 'mathlib': latest})
        self.acquire()
        self.assertEqual(self.affected(new_pins={'Aglib': self.a_pin, 'mathlib': latest}),
                         set(self.current) - {'Tiny.Unrelated'})

    def test_wrong_head_dirty_worktree_never_supplies_source_edges(self):
        self.acquire()
        package = self.root / '.lake/packages/mathlib'
        self.git(package, 'checkout', '--detach', self.old_b['rev'])
        (package / 'Mathlib/X.lean').write_text('import Unknown.Dirty\n')
        provider = self.root / '.lake/packages/Aglib/Aglib/Provider.lean'
        provider.write_text('import Unknown.WrongHead\n')
        before = self.git(package, 'rev-parse', 'HEAD'), (package / 'Mathlib/X.lean').read_bytes()
        self.assertEqual(self.affected(), set(self.current) - {'Tiny.Unrelated'})
        self.acquire()
        self.assertEqual((self.git(package, 'rev-parse', 'HEAD'), (package / 'Mathlib/X.lean').read_bytes()), before)

    def test_missing_current_objects_fetch_is_metadata_only_for_existing_worktree(self):
        self.acquire()
        package = self.root / '.lake/packages/mathlib'
        (self.b / 'Mathlib/X.lean').write_text('import Init\ndef x := 3\n')
        self.commit(self.b)
        latest = self.pin('mathlib', self.b)
        self.write_manifest({'Aglib': self.a_pin, 'mathlib': latest})
        (package / 'Mathlib/X.lean').write_text('dirty retained bytes\n')
        before = self.git(package, 'rev-parse', 'HEAD'), (package / 'Mathlib/X.lean').read_bytes()
        self.acquire()
        self.assertEqual((self.git(package, 'rev-parse', 'HEAD'), (package / 'Mathlib/X.lean').read_bytes()), before)
        self.assertEqual(self.git(package, 'cat-file', '-t', latest['rev']), 'commit')

    def test_empty_existing_directory_is_not_source_evidence(self):
        (self.root / '.lake/packages/mathlib').mkdir(parents=True)
        with self.assertRaisesRegex(ValueError, 'not its own Git'):
            self.acquire()

    def test_invalid_or_unavailable_url_and_revision_are_errors(self):
        for url, rev in [('file:///definitely/missing/repository', self.new_b['rev']),
                         (str(self.b), 'f' * 40)]:
            with self.subTest(url=url, rev=rev):
                shutil.rmtree(self.root / '.lake', ignore_errors=True)
                pins = {'mathlib': dict(self.new_b, url=url, rev=rev)}
                with self.assertRaisesRegex(ValueError, 'Git command failed'):
                    self.acquire(old_pins=pins, new_pins=pins)
        with self.assertRaisesRegex(ValueError, 'HTTPS'):
            resolve_planning_sources(self.root, self.config, self.base,
                                     workspace=self.workspace, old_pins=self.old_pins, new_pins=self.new_pins)

    def test_source_roots_subdir_and_toml_srcdir_come_from_pinned_objects(self):
        repo = self.repo('subdir', {'nested/lakefile.toml': 'name="Nested"\n[[lean_lib]]\nname="Actual"\nsrcDir="source"\n',
                                    'nested/source/Actual/P.lean': 'import Init\n'})
        pin = dict(self.pin('unrelated-package-name', repo), subDir='nested')
        pins = {pin['name']: pin}
        self.current = {'Tiny.P': {'workspace': 'root', 'imports': ['Actual.P']},
                        'Tiny.Unrelated': self.current['Tiny.Unrelated']}
        self.old = self.current
        self.acquire(old_pins=pins, new_pins=pins)
        self.assertEqual(self.affected(changed=(pin['name'],), old_pins=pins, new_pins=pins), {'Tiny.P'})

    def test_selection_has_no_network_or_mutating_git_commands(self):
        self.acquire()
        actual = subprocess.run
        calls = []
        def observed(command, **kwargs):
            calls.append(command)
            self.assertEqual(kwargs['env']['GIT_NO_REPLACE_OBJECTS'], '1')
            return actual(command, **kwargs)
        with patch('lean_ci.project.dependencies.subprocess.run', side_effect=observed):
            self.affected()
        self.assertFalse(any(any(action in c for action in ('fetch', 'checkout', 'clone')) for c in calls))

    def test_changed_owner_needs_no_math_bodies_and_unchanged_pin_imports_read_once(self):
        self.acquire()
        with patch.object(dependencies, '_blobs', wraps=dependencies._blobs) as blobs:
            self.assertEqual(self.affected(), set(self.current) - {'Tiny.Unrelated'})
        requests = [(str(call.args[0]), call.args[2]) for call in blobs.call_args_list]
        self.assertFalse(any(path.endswith('.lean') for repo, paths in requests if repo.endswith('/mathlib') for path in paths))
        self.assertEqual(sum('Aglib/Provider.lean' in paths for _, paths in requests), 1)

    def test_resolver_uses_historical_package_coordinates_when_root_moves(self):
        configuration = self.root / '.github/lean-ci.toml'
        configuration.parent.mkdir()
        configuration.write_text('schema=1\npackage_dir="."\n[roles]\nproduction=["Tiny"]\n')
        self.write_manifest(self.old_pins)
        base = self.commit(self.root)
        package = self.root / 'lean'
        package.mkdir()
        (self.root / 'lake-manifest.json').rename(package / 'lake-manifest.json')
        (package / 'lake-manifest.json').write_text(json.dumps({'name': 'Tiny', 'packages': list(self.new_pins.values())}))
        configuration.write_text('schema=1\npackage_dir="lean"\n[roles]\nproduction=["Tiny"]\n')
        workspace = dict(self.workspace, path='lean')
        config = dict(self.config, package_dir='lean', workspaces=[workspace])
        result = resolve_planning_sources(self.root, config, base, allow_local=True)
        self.assertEqual({row['revision'] for row in result['fetched']},
                         {self.a_pin['rev'], self.old_b['rev'], self.new_b['rev']})
        self.assertTrue((package / '.lake/packages/mathlib/Mathlib/X.lean').is_file())

    def test_path_dependency_cannot_silently_disappear_from_external_evidence(self):
        invalid = {'Foreign': {'name': 'Foreign', 'type': 'path', 'dir': '../../outside'}}
        with self.assertRaisesRegex(DependencySourcesUnavailable, 'exact configured parent'):
            self.affected(old_pins=invalid, new_pins=invalid)

    def test_missing_pinned_source_blob_is_typed_and_recovered_without_checkout(self):
        self.acquire()
        package = self.root / '.lake/packages/Aglib'
        blob = self.git(package, 'rev-parse', self.a_pin['rev'] + ':Aglib/Provider.lean')
        loose = package / '.git/objects' / blob[:2] / blob[2:]
        self.assertTrue(loose.is_file(), 'tiny fixture should use loose fetched objects')
        loose.unlink()
        before = self.git(package, 'rev-parse', 'HEAD'), (package / 'Aglib/Provider.lean').read_bytes()
        with self.assertRaises(DependencySourcesUnavailable):
            self.affected()
        self.acquire()
        self.assertEqual(self.affected(), set(self.current) - {'Tiny.Unrelated'})
        self.assertEqual((self.git(package, 'rev-parse', 'HEAD'), (package / 'Aglib/Provider.lean').read_bytes()), before)

    def test_new_origin_uses_current_pin_url_and_existing_custom_origin_cache_are_preserved(self):
        current_source = self.directory / 'current-source'
        self.git(self.directory, 'clone', '--no-local', str(self.b), str(current_source))
        current_pin = dict(self.new_b, url=str(current_source))
        self.acquire(old_pins=self.old_pins, new_pins={'Aglib': self.a_pin, 'mathlib': current_pin})
        package = self.root / '.lake/packages/mathlib'
        self.assertEqual(self.git(package, 'remote', 'get-url', 'origin'), str(current_source))
        self.git(package, 'remote', 'set-url', 'origin', 'https://example.invalid/custom-origin')
        cache = package / '.lake/build/lib/lean/Mathlib/X.olean'
        cache.parent.mkdir(parents=True)
        cache.write_bytes(b'retained native cache')
        source = package / 'Mathlib/X.lean'
        source.write_text('dirty source retained\n')
        before = self.git(package, 'rev-parse', 'HEAD'), source.read_bytes(), cache.read_bytes()
        (current_source / 'Mathlib/X.lean').write_text('import Init\ndef x := 3\n')
        self.commit(current_source)
        latest = self.pin('mathlib', current_source)
        self.acquire(old_pins=self.old_pins, new_pins={'Aglib': self.a_pin, 'mathlib': latest})
        self.assertEqual(self.git(package, 'remote', 'get-url', 'origin'), 'https://example.invalid/custom-origin')
        self.assertEqual((self.git(package, 'rev-parse', 'HEAD'), source.read_bytes(), cache.read_bytes()), before)
        self.assertEqual(self.git(package, 'cat-file', '-t', latest['rev']), 'commit')


if __name__ == '__main__':
    unittest.main()
