"""Regress version-independent CI keys and isolated project-cache preparation."""
import json
from pathlib import Path
import tempfile
import unittest

from functools import partial
from lean_ci.checks.replay_cache import config_hash as _config_hash
config_hash = partial(_config_hash, packages=('', 'examples/downstream/'))


class CacheFixture(unittest.TestCase):
    def setUp(self):
        temporary_root = '/private/tmp' if Path('/private/tmp').is_dir() else None
        self.tmp = tempfile.TemporaryDirectory(prefix='ag-ci-cache-', dir=temporary_root)
        self.root = Path(self.tmp.name)
        for package in (Path('.'), Path('examples/downstream')):
            directory = self.root / package
            directory.mkdir(parents=True, exist_ok=True)
            (directory / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            (directory / 'lake-manifest.json').write_text('{"packages": []}\n')
            (directory / 'lakefile.toml').write_text(
                'name = "fixture"\nversion = "0.1.0"\nvalues = ["a", "b"]\n'
                '[[lean_lib]]\nname = "Aglib"\n')
        for name in ('Aglib', 'Aglib/Current', 'AglibTest', 'AglibTest/Positive',
                     'AglibTest/AuditSupport', 'AglibTest/Axioms',
                     'AglibTest/NegativeControls/Bad', 'examples/downstream/Consumer',
                     'examples/downstream/Consumer/Current', 'examples/downstream/Audit'):
            path = self.root / (name + '.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('module\n')

    def tearDown(self):
        self.tmp.cleanup()



    def config(self, text, package=''):
        (self.root / package / 'lakefile.toml').write_text(text)


class CacheKeyTests(CacheFixture):
    def test_only_top_level_package_versions_are_ignored_in_both_packages(self):
        original = config_hash(self.root)
        for package in ('', 'examples/downstream'):
            path = self.root / package / 'lakefile.toml'
            path.write_text(path.read_text().replace('version = "0.1.0"', 'version = "4.9.2"'))
            self.assertEqual(config_hash(self.root), original)
        path.write_text(path.read_text() + '\n[options]\nversion = "important"\n')
        self.assertNotEqual(config_hash(self.root), original)

    def test_scalar_types_do_not_collide(self):
        digests = []
        for value in ('true', '1', '"1"', '1.0', '"true"'):
            self.config('name = "fixture"\nvalue = ' + value + '\n')
            digests.append(config_hash(self.root))
        self.assertEqual(len(set(digests)), len(digests))

    def test_native_storage_policy_absent_true_false_preserves_legacy_key(self):
        baseline = config_hash(self.root)
        for package in ('', 'examples/downstream'):
            path = self.root / package / 'lakefile.toml'
            original = path.read_text()
            for enabled in (None, True, False):
                for restored in (None, True, False):
                    flags = ''.join(f'{name} = {str(value).lower()}\n'
                                    for name, value in [('enableArtifactCache', enabled),
                                                        ('restoreAllArtifacts', restored)]
                                    if value is not None)
                    with self.subTest(package=package, enabled=enabled, restored=restored):
                        path.write_text(flags + original)
                        self.assertEqual(config_hash(self.root), baseline)
            path.write_text(original)

    def test_nested_storage_named_fields_remain_significant(self):
        baseline = config_hash(self.root)
        for package in ('', 'examples/downstream'):
            path = self.root / package / 'lakefile.toml'
            original = path.read_text()
            for table in ('[leanOptions]', '[[require]]\nname="dependency"'):
                for field in ('enableArtifactCache', 'restoreAllArtifacts'):
                    digests = []
                    for value in ('true', 'false'):
                        path.write_text(original + f'\n{table}\n{field}={value}\n')
                        digests.append(config_hash(self.root))
                    self.assertNotIn(baseline, digests)
                    self.assertNotEqual(*digests)
            path.write_text(original)

    def test_table_order_and_comments_are_normalized_but_array_order_is_not(self):
        self.config('name="fixture"\nvalues=["a", "b"]\n')
        original = config_hash(self.root)
        self.config('# comment\nvalues = ["a", "b"]\nname = "fixture"\n')
        self.assertEqual(config_hash(self.root), original)
        self.config('name="fixture"\nvalues=["b", "a"]\n')
        self.assertNotEqual(config_hash(self.root), original)

    def test_options_dependencies_and_each_package_toolchain_affect_key(self):
        for package in ('', 'examples/downstream'):
            for name, addition in (
                    ('lakefile.toml', '\n[leanOptions]\nautoImplicit=false\n'),
                    ('lakefile.toml', '\n[[require]]\nname="new-dependency"\nrev="new-pin"\n'),
                    ('lean-toolchain', 'different-toolchain\n'),
                    ('lake-manifest.json', ' ')):
                with self.subTest(package=package, name=name, addition=addition):
                    path = self.root / package / name
                    original_bytes = path.read_bytes()
                    original = config_hash(self.root)
                    path.write_bytes(original_bytes + addition.encode())
                    self.assertNotEqual(config_hash(self.root), original)
                    path.write_bytes(original_bytes)

    def test_executable_configuration_is_always_raw(self):
        for package in ('', 'examples/downstream'):
            path = self.root / package / 'lakefile.lean'
            absent = config_hash(self.root)
            path.write_text('-- executable package config\n')
            present = config_hash(self.root)
            self.assertNotEqual(present, absent)
            path.write_text('-- executable package config changed\n')
            self.assertNotEqual(config_hash(self.root), present)

    def test_missing_empty_malformed_and_unsupported_configuration_fail(self):
        for package in ('', 'examples/downstream'):
            for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
                path = self.root / package / name
                original = path.read_bytes()
                path.unlink()
                with self.assertRaises(OSError):
                    config_hash(self.root)
                path.write_bytes(b' ')
                with self.assertRaises(ValueError):
                    config_hash(self.root)
                path.write_bytes(original)
        for invalid in ('name = [', 'name="fixture"\nvalue=nan\n'):
            self.config(invalid)
            with self.assertRaises(ValueError):
                config_hash(self.root)


if __name__ == '__main__':
    unittest.main()
