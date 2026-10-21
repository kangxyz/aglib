"""Configuration contract fixtures; no Lean invocation is required."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from lean_ci.project.configuration import load_config


class Fixture(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='lean-ci-config-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.write('lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('lakefile.toml', 'name="Tiny"\n[[lean_lib]]\nname="Tiny"\n[[lean_lib]]\nname="TinyTest"\n')
        self.write('Tiny/Base.lean', 'module\ndef base := 1\n')
        self.write('Tiny/Consumer.lean', 'module\npublic import Tiny.Base\ndef consumer := base\n')
        self.write('Tiny.lean', 'module\npublic import Tiny.Consumer\n')
        self.write('TinyTest/Positive.lean', 'import Tiny.Consumer\nexample : consumer = 1 := rfl\n')
        self.write('.github/lean-ci.toml', 'schema=1\npackage_dir="."\n[roles]\nproduction=["Tiny"]\ntests=["TinyTest"]\n')

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def git(self, *arguments):
        return subprocess.check_output(['git', *arguments], cwd=self.root, stderr=subprocess.DEVNULL).decode().strip()

    def commit(self):
        if not (self.root / '.git').exists():
            self.git('init', '-q')
            self.git('config', 'user.name', 'CI fixture')
            self.git('config', 'user.email', 'ci@example.invalid')
        self.git('add', '.')
        self.git('commit', '-qm', 'fixture')
        return self.git('rev-parse', 'HEAD')


class ConfigurationTests(Fixture):
    def test_json_data_and_exact_roles(self):
        value = load_config(self.root)
        self.assertEqual(value['modules']['Tiny.Base']['role'], 'production')
        self.assertEqual(value['modules']['TinyTest.Positive']['role'], 'tests')
        self.assertEqual(json.loads(json.dumps(value)), value)

    def test_unknown_key_and_callback_rejected(self):
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('[roles]', 'command="run arbitrary"\n[roles]'))
        with self.assertRaisesRegex(ValueError, 'Unknown'):
            load_config(self.root)

    def test_missing_library_owner_rejected(self):
        with (self.root / 'lakefile.toml').open('a') as stream:
            stream.write('[[lean_lib]]\nname="Unowned"\n')
        with self.assertRaisesRegex(ValueError, 'Unowned Lake'):
            load_config(self.root)

    def test_missing_source_owner_rejected(self):
        self.write('Tools/Driver.lean', 'def driver := 1\n')
        with self.assertRaisesRegex(ValueError, 'Unowned Lean'):
            load_config(self.root)

    def test_extra_support_never_becomes_lake_module(self):
        self.write('Tools/Driver.lean', 'def driver := 1\n')
        with (self.root / '.github/lean-ci.toml').open('a') as stream:
            stream.write('[sources]\nsupport=["Tools"]\n')
        value = load_config(self.root)
        self.assertNotIn('Tools.Driver', value['modules'])
        self.assertEqual(value['extra_sources'], [{'path': 'Tools/Driver.lean', 'role': 'support'}])

    def test_duplicate_role_rejected(self):
        with (self.root / '.github/lean-ci.toml').open('a') as stream:
            stream.write('support=["Tiny"]\n')
        with self.assertRaisesRegex(ValueError, 'multiply owned'):
            load_config(self.root)

    def test_path_escape_rejected(self):
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('package_dir="."', 'package_dir="../outside"'))
        with self.assertRaisesRegex(ValueError, 'escaping'):
            load_config(self.root)

    def test_symlink_source_rejected(self):
        (self.root / 'Tiny/Shadow.lean').symlink_to(self.root / 'Tiny/Base.lean')
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            load_config(self.root)

    def test_custom_source_directory_and_roots(self):
        self.write('lakefile.toml', 'name="Tiny"\n[[lean_lib]]\nname="Prod"\nsrcDir="lib"\nroots=["Real"]\n[[lean_lib]]\nname="TinyTest"\n')
        self.write('lib/Real.lean', 'def real := 1\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('["Tiny"]', '["Prod"]') + '[sources]\nsupport=["Tiny", "Tiny.lean"]\n')
        value = load_config(self.root)
        self.assertEqual(value['modules']['Real']['path'], 'lib/Real.lean')

    def test_formal_control_and_expected_failure_are_disjoint(self):
        self.write('TinyTest/Negative.lean', '#check missing\n')
        self.write('TinyTest/Formal.lean', 'def formal := 2\n')
        self.write('TinyTest/Control.lean', 'def control := 3\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('[roles]', 'expected_failure=["TinyTest/Negative.lean"]\nformal_only=["TinyTest/Formal.lean"]\ncontrols=["TinyTest/Control.lean"]\n[roles]'))
        value = load_config(self.root)
        self.assertEqual(value['modules']['TinyTest.Negative']['role'], 'expected_failure')
        self.assertEqual(value['modules']['TinyTest.Formal']['role'], 'formal_only')
        self.assertEqual(value['modules']['TinyTest.Control']['role'], 'control')

    def test_wrong_toolchain_rejected(self):
        self.write('lean-toolchain', 'leanprover/lean4:v4.33.0\n')
        with self.assertRaisesRegex(ValueError, '4.34.1'):
            load_config(self.root)

    def add_client(self):
        self.write('examples/downstream/lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('examples/downstream/lakefile.toml', 'name="client"\n[[lean_lib]]\nname="Consumer"\n')
        self.write('examples/downstream/Consumer.lean', 'import Tiny.Base\ndef client := base\n')
        self.write('Tiny/Consumer.lean', 'import Tiny.Base\ndef consumer := base\n')
        with (self.root / '.github/lean-ci.toml').open('a') as stream:
            stream.write('[[clients]]\nid="downstream"\npath="examples/downstream"\n[clients.roles]\nproduction=["Consumer"]\n')

    def test_client_identity_is_package_qualified(self):
        self.add_client()
        value = load_config(self.root)
        self.assertEqual(value['modules']['downstream:Consumer']['workspace'], 'downstream')
        self.assertEqual(value['modules']['Tiny.Consumer']['workspace'], 'root')

    def test_reference_sources_do_not_become_current_sources(self):
        self.write('docs/provenance/Old.lean', 'sorry historical text\n')
        with (self.root / '.github/lean-ci.toml').open('a') as stream:
            stream.write('[sources]\nreferences=["docs/provenance"]\n')
        value = load_config(self.root)
        self.assertEqual(value['extra_sources'], [{'path': 'docs/provenance/Old.lean', 'role': 'references'}])

    def test_reference_cannot_hide_current_lake_source(self):
        with (self.root / '.github/lean-ci.toml').open('a') as stream:
            stream.write('[sources]\nreferences=["Tiny/Base.lean"]\n')
        with self.assertRaisesRegex(ValueError, 'overlaps'):
            load_config(self.root)

    def test_quoted_literal_module_component_roundtrips(self):
        self.write('Tiny/odd.name.lean', 'def quoted := 1\n')
        value = load_config(self.root)
        self.assertEqual(value['modules']['Tiny.«odd.name»']['path'], 'Tiny/odd.name.lean')

    def test_direct_dependency_manifest_disagreement_rejected(self):
        with (self.root / 'lakefile.toml').open('a') as stream:
            stream.write('[[require]]\nname="dep"\ngit="https://example.invalid/dep"\nrev="' + 'a' * 40 + '"\n')
        self.write('lake-manifest.json', json.dumps({'packages': [{'name': 'dep', 'type': 'git', 'rev': 'b' * 40, 'inputRev': 'a' * 40, 'url': 'https://example.invalid/dep', 'inherited': False}]}))
        with self.assertRaisesRegex(ValueError, 'mismatch'):
            load_config(self.root)

    def test_unsupported_axiom_policy_is_rejected_not_ignored(self):
        self.write('policy/axioms.json', '{}\n')
        with (self.root / '.github/lean-ci.toml').open('a') as stream:
            stream.write('[policy]\naxioms=["policy/axioms.json"]\n')
        with self.assertRaisesRegex(ValueError, 'unsupported'):
            load_config(self.root)

    def test_admitted_json_config_uses_the_same_schema(self):
        import tomllib
        data = tomllib.loads((self.root / '.github/lean-ci.toml').read_text())
        self.write('.lean-ci/config.json', json.dumps(data))
        toml_config = load_config(self.root)
        json_config = load_config(self.root, '.lean-ci/config.json')
        json_config['config_path'] = toml_config['config_path']
        self.assertEqual(toml_config, json_config)

    def test_json_config_duplicate_keys_are_rejected(self):
        self.write('.lean-ci/config.json', '{"schema":1,"schema":1}')
        with self.assertRaisesRegex(ValueError, 'Duplicate configuration key'):
            load_config(self.root, '.lean-ci/config.json')
