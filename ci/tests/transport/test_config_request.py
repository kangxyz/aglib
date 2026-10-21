"""Flat config-native transport fixtures; no compiler, network or remote job."""
import copy
import json
import shutil
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from lean_ci.project.configuration import load_config
from lean_ci.application import implementation_identity
from lean_ci.transport.frozen import admit, execute
from lean_ci.transport.request import (CONFIG, MANIFEST, PROJECTION, REQUEST, create_request,
    load_request_application)
from lean_ci.execution.state import TemporalInputs, digest, file_hash, write_json
import tests.execution.test_engine as fixtures


class ConfigRequestTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='lean-ci-native-bundle-')
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name).resolve()
        self.root = self.directory / 'repo'
        self.root.mkdir()
        self.write('lean/lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('lean/lakefile.toml', 'name="Tiny"\n[[lean_lib]]\nname="Tiny"\n[[lean_lib]]\nname="TinyTest"\n')
        self.write('lean/lake-manifest.json', '{"packages":[]}\n')
        self.write('lean/Tiny/Base.lean', 'module\ndef base := 1\n')
        self.write('lean/Tiny/Consumer.lean', 'module\npublic import Tiny.Base\ndef consumer := base\n')
        self.write('lean/TinyTest/Positive.lean', 'import Tiny.Consumer\nexample : consumer = 1 := rfl\n')
        self.write('lean/scripts/Driver.lean', 'def driver := 1\n')
        self.write('research/Archived.lean', 'axiom archived : False\n')
        self.write('.github/source.json', json.dumps({'schema': 1, 'kind': 'source_exceptions',
            'legacy_auditors': ['lean/scripts/Driver.lean'],
            'private_imports': {'lean/Tiny/Base.lean': ['import all Fixture']}}))
        self.write('.github/budget.json', json.dumps({'schema': 1, 'kind': 'budget',
            'legacy': {'lean/Tiny/Base.lean': [300000]}}))
        self.write('.github/style.json', '{"schema":1,"kind":"source"}\n')
        self.write('.github/lean-ci.toml', '''schema=1
package_dir="lean"
[roles]
production=["Tiny"]
tests=["TinyTest"]
[sources]
support=["lean/scripts"]
references=["research"]
[policy]
exceptions=[".github/source.json"]
budget=[".github/budget.json"]
style=[".github/style.json"]
''')
        self.git('init', '-q')
        self.git('config', 'user.name', 'Native transport fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.git('add', '.')
        self.git('commit', '-qm', 'fixture')
        self.bundle = self.directory / 'bundle'
        self.manifest_path = self.directory / 'SOURCE.json'

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def git(self, *arguments):
        return subprocess.check_output(['git', *arguments], cwd=self.root, text=True).strip()

    def produce(self, targets=('Tiny.Base',)):
        self.result = create_request(self.root, targets=targets, bundle=self.bundle)
        self.source()
        return self.result

    def source(self):
        paths = {p.relative_to(self.bundle).as_posix(): file_hash(p)
                 for p in self.bundle.rglob('*') if p.is_file() and p.name != MANIFEST}
        transport = json.loads((self.bundle / MANIFEST).read_text()) if (self.bundle / MANIFEST).exists() else {}
        transport.update(schema=1, files=paths, content_sha256=digest(paths), git_head=self.git('rev-parse', 'HEAD'))
        write_json(self.bundle / MANIFEST, transport)
        paths[MANIFEST] = file_hash(self.bundle / MANIFEST)
        self.expected = digest(paths)
        self.manifest = {'workspace': str(self.bundle), 'files': paths,
                         'content_sha256': self.expected, 'git_head': self.git('rev-parse', 'HEAD')}
        write_json(self.manifest_path, self.manifest)

    def load(self):
        observations = TemporalInputs()
        result = admit(self.bundle / REQUEST, self.manifest_path, self.expected, observations)
        _, manifest, request, adapter, root, package, admitted = result
        self.assertIsNone(adapter)
        return load_request_application(root, package, request, manifest, admitted, observations)

    def update_json(self, path, change):
        value = json.loads((self.bundle / path).read_text())
        change(value)
        write_json(self.bundle / path, value)
        self.source()

    def test_flat_package_preserves_source_bytes_full_enrollment_and_metadata(self):
        result = self.produce()
        self.assertEqual(result['source_content_sha256'], self.expected)
        self.assertEqual((self.bundle / 'Tiny/Base.lean').read_bytes(), (self.root / 'lean/Tiny/Base.lean').read_bytes())
        self.assertTrue((self.bundle / 'TinyTest/Positive.lean').is_file())
        self.assertTrue((self.bundle / 'scripts/Driver.lean').is_file())
        self.assertFalse((self.bundle / '.git').exists())
        self.assertFalse((self.bundle / 'research').exists())
        self.assertFalse(any(p.suffix in {'.py', '.olean', '.so'} for p in self.bundle.rglob('*')))
        config = load_config(self.bundle, CONFIG)
        self.assertEqual(config['package_dir'], '.')
        self.assertEqual(config['sources']['references'], [])
        projection = json.loads((self.bundle / PROJECTION).read_text())
        self.assertEqual(projection['excluded_references'], ['research'])
        self.assertEqual(projection['path_mapping']['lean/Tiny/Base.lean'], 'Tiny/Base.lean')
        self.assertIn('TinyTest.Positive', result['scope']['modules'])
        self.assertEqual(set(result['sync_includes']), set(self.manifest['files']))

    def test_typed_policy_paths_project_and_original_data_stays_unchanged(self):
        original = (self.root / '.github/source.json').read_bytes()
        self.produce()
        config = load_config(self.bundle, CONFIG)
        exceptions = json.loads((self.bundle / config['policy']['exceptions'][0]).read_text())
        self.assertEqual(exceptions['legacy_auditors'], ['scripts/Driver.lean'])
        self.assertEqual(set(exceptions['private_imports']), {'Tiny/Base.lean'})
        budget = json.loads((self.bundle / config['policy']['budget'][0]).read_text())
        self.assertEqual(set(budget['legacy']), {'Tiny/Base.lean'})
        self.assertEqual((self.root / '.github/source.json').read_bytes(), original)
        self.load()

    def test_git_free_loader_uses_common_factory_without_repository_python(self):
        self.produce()
        with patch('lean_ci.project.scope.git', side_effect=AssertionError('Git forbidden')), \
             patch('lean_ci.transport.frozen.importlib.util.spec_from_file_location', side_effect=AssertionError('adapter forbidden')):
            application = self.load()
            request = json.loads((self.bundle / REQUEST).read_text())
            tasks = application._tasks(request['payload'], 'native', self.directory / 'tasks')
        self.assertEqual(type(application.adapter).__name__, 'ConfiguredAdapter')
        self.assertTrue(all(t.get('native') is not False for t in tasks))
        self.assertTrue(any(t.get('check_kind') == 'declarations' for t in tasks))
        self.assertTrue(any('R5_LEAN_REMOTE_PROFILE' == k for k in application.runtime.resource_config.profile_keys))

    def test_missing_or_corrupted_declared_source_is_rejected_before_factory(self):
        self.produce()
        (self.bundle / 'Tiny/Base.lean').write_text('def forged := 0\n')
        with self.assertRaisesRegex(ValueError, 'bytes differ'):
            self.load()
        (self.bundle / 'Tiny/Base.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing'):
            self.load()

    def test_rehashed_tampered_projection_cannot_change_typed_policy(self):
        self.produce()
        config = load_config(self.bundle, CONFIG)
        self.update_json(config['policy']['exceptions'][0], lambda data: data.update(legacy_auditors=[]))
        with self.assertRaisesRegex(ValueError, 'typed original'):
            self.load()

    def test_rehashed_forged_scope_membership_or_missing_required_checks_rejected(self):
        self.produce()
        original = (self.bundle / REQUEST).read_bytes()
        for change, message in [(lambda r: r['payload']['scope']['providers'].append('Other.Unadmitted'), 'membership'),
                                (lambda r: r['payload']['scope'].update(declarations=[]), 'defining-origin')]:
            with self.subTest(message=message):
                (self.bundle / REQUEST).write_bytes(original)
                self.update_json(REQUEST, change)
                with self.assertRaisesRegex(ValueError, message):
                    self.load()

    def test_ambient_adapter_field_rejected_in_schema2(self):
        self.produce()
        self.update_json(REQUEST, lambda r: r.update(adapter='ambient.py'))
        with self.assertRaisesRegex(ValueError, 'schema/fields'):
            self.load()

    def test_optional_unadmitted_nolints_cannot_enter_native_predicate(self):
        self.produce()
        self.write('lean/scripts/nolints.json', '[]')
        path = self.bundle / 'scripts/nolints.json'
        path.write_text('[]')
        # Rehashing outer SOURCE alone must not override declared absent inputs.
        files = dict(self.manifest['files'], **{'scripts/nolints.json': file_hash(path)})
        self.expected = digest(files)
        write_json(self.manifest_path, dict(self.manifest, files=files, content_sha256=self.expected))
        with self.assertRaisesRegex(ValueError, 'absent native input'):
            self.load()

    def test_source_symlink_escape_and_existing_destination_are_rejected(self):
        subject = self.root / 'lean/Tiny/Base.lean'
        subject.unlink()
        subject.symlink_to(self.root / 'lean/Tiny/Consumer.lean')
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            self.produce()
        subject.unlink(); subject.write_text('def base := 1\n')
        self.produce()
        with self.assertRaisesRegex(ValueError, 'must not already exist'):
            create_request(self.root, targets=['Tiny.Base'], bundle=self.bundle)

    def test_captured_heartbeat_package_relative_keys_do_not_get_double_prefix(self):
        self.write('.github/budget.json', json.dumps({'schema_version': 1, 'maxHeartbeats': 200000,
            'source_head': 'a' * 40, 'captured_at': '2026-10-21T00:00:00Z',
            'legacy': {'Tiny/Base.lean': [300000]}}))
        self.produce()
        config = load_config(self.bundle, CONFIG)
        budget = json.loads((self.bundle / config['policy']['budget'][0]).read_text())
        self.assertEqual(set(budget['legacy']), {'Tiny/Base.lean'})
        self.load()

    def test_same_root_client_pins_coordinates_and_source_bytes_are_preserved(self):
        for path in list((self.root / 'lean').iterdir()):
            shutil.move(str(path), str(self.root / path.name))
        (self.root / 'lean').rmdir()
        config_path = self.root / '.github/lean-ci.toml'
        config_path.write_text(config_path.read_text().replace('package_dir="lean"', 'package_dir="."').replace('lean/scripts', 'scripts') + '\n[[clients]]\nid="client"\npath="examples/client"\n[clients.roles]\nproduction=["Client"]\n')
        for name in ('source', 'budget'):
            path = self.root / ('.github/' + name + '.json')
            path.write_text(path.read_text().replace('lean/', ''))
        self.write('examples/client/lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('examples/client/lakefile.toml', 'name="client"\n[[lean_lib]]\nname="Client"\n[[require]]\nname="Tiny"\npath="../.."\n')
        self.write('examples/client/lake-manifest.json', '{"packages":[{"type":"path","name":"Tiny","dir":"../.."}]}')
        self.write('examples/client/Client/Use.lean', 'import Tiny.Base\ndef client := base\n')
        self.produce(targets=('Tiny.Base', 'client:Client.Use'))
        self.assertIn('client:Client.Use', self.result['scope']['source_check'])
        application = self.load()
        config = application.adapter.config(self.bundle)
        self.assertEqual(config['clients'][0]['path'], 'examples/client')
        self.assertEqual(self.result['scope']['clients']['client'], ['client:Client.Use'])
        self.assertEqual((self.bundle / 'examples/client/lakefile.toml').read_bytes(), (self.root / 'examples/client/lakefile.toml').read_bytes())
        self.assertEqual((self.bundle / 'examples/client/lake-manifest.json').read_bytes(), (self.root / 'examples/client/lake-manifest.json').read_bytes())

    def test_extra_source_check_path_projects_but_old_source_diagnostics_remain_original(self):
        self.write('lean/Tiny/Base.lean', 'module\ndef base := 2\n')
        self.write('lean/scripts/Driver.lean', 'def driver := 2\n')
        self.write('.github/style.json', '{"schema":1,"kind":"source","broad_facades":false}\n')
        self.produce(targets=())
        self.assertIn('scripts/Driver.lean', self.result['scope']['source_check'])
        self.assertNotIn('lean/scripts/Driver.lean', self.result['scope']['source_check'])
        self.assertIn('Tiny.Base', self.result['scope']['source_check'])
        self.assertIn('TinyTest.Positive', self.result['scope']['source_check'])
        diagnostic = {'baseline_enrollment', 'enrollment_changes', 'policy_changes'}
        self.assertTrue(diagnostic.isdisjoint(self.result['scope']))
        projection = json.loads((self.bundle / PROJECTION).read_text())
        original = projection['original_scope']
        self.assertIn('lean/scripts/Driver.lean', original['source_check'])
        self.assertTrue(diagnostic.issubset(original))
        self.assertEqual(original['baseline_enrollment'], 'present')
        self.assertEqual(original['policy_changes']['style']['after'][0][0], '.github/style.json')
        self.assertEqual(set(self.result['scope']['modules']), {'Tiny.Base', 'Tiny.Consumer', 'TinyTest.Positive'})
        self.load()

    def test_source_policy_only_obligations_cannot_become_native_request(self):
        self.write('.github/style.json', '{"schema":1,"kind":"source","broad_facades":false}\n')
        with self.assertRaisesRegex(ValueError, 'source-only obligations remain separate'):
            self.produce(targets=())
        self.assertFalse(self.bundle.exists())

    def test_rehashed_source_selector_cannot_admit_ambient_paths_or_unknown_keys(self):
        self.produce()
        original = (self.bundle / REQUEST).read_bytes()
        for change, message in [
                (lambda r: r['payload']['scope']['source_check'].append('research/Archived.lean'), 'membership'),
                (lambda r: r['payload']['scope'].update(source_check=[]), 'omit selected source-style'),
                (lambda r: r['payload']['scope'].update(unadmitted_selector=[]), 'scope fields')]:
            with self.subTest(message=message):
                (self.bundle / REQUEST).write_bytes(original)
                self.update_json(REQUEST, change)
                with self.assertRaisesRegex(ValueError, message):
                    self.load()

    def test_native_only_execute_and_receipt_reverification_keep_source_claim_separate(self):
        # A changed independent support declaration selects native source style,
        # while source-policy-only edits correctly remain source-only obligations.
        lake = self.root / 'lean/lakefile.toml'
        lake.write_text(lake.read_text() + '\n[[lean_lib]]\nname="Support"\n')
        config = self.root / '.github/lean-ci.toml'
        config.write_text(config.read_text().replace('[sources]', 'support=["Support"]\n[sources]'))
        self.write('lean/Support/StyleOnly.lean', 'def support := 1\n')
        self.git('add', '.'); self.git('commit', '-qm', 'prepared support declaration')
        self.write('lean/Support/StyleOnly.lean', 'def support := 2\n')
        self.produce(targets=())
        runner = fixtures.FixtureExecutor(self.bundle)
        with patch('lean_ci.execution.runtime.NativeRuntime.compiler_identity', return_value=fixtures.TOOLCHAIN), \
             patch('lean_ci.execution.runtime.NativeRuntime.run', side_effect=runner.run), \
             patch('lean_ci.application.git', side_effect=AssertionError('Git forbidden')), \
             patch('lean_ci.project.scope.git', side_effect=AssertionError('Git forbidden')):
            first = execute(self.bundle / REQUEST, source_manifest=self.manifest_path,
                            expected_source=self.expected, state=self.directory / 'state')
            calls = list(runner.calls)
            verified = execute(self.bundle / REQUEST, source_manifest=self.manifest_path,
                               expected_source=self.expected, state=self.directory / 'state', verify_only=True)
        self.assertEqual(runner.calls, calls)
        self.assertTrue(first['performed_checks'])
        self.assertTrue(verified['verification_only'])
        self.assertIn('separate', first['source_checks'])
        self.assertEqual(first['source_basis']['kind'], 'transport-snapshot')
        self.assertFalse((self.directory / 'state/complete.json').exists())


if __name__ == '__main__':
    unittest.main()
