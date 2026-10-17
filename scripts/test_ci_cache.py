"""Regress version-independent CI keys and isolated project-cache preparation."""
import json
from pathlib import Path
import tempfile
import unittest

from cache_key import config_hash
from check_compiled_inventory import check_inventory
from prepare_build_cache import prepare, STAMP
from resource_guard import limits


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

    def artifact(self, name, package='', directory='lib/lean', suffix='.olean'):
        path = self.root / package / '.lake/build' / directory / (name + suffix)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b'cached project output')
        return path

    def prepare(self, compiler='Lean fixture compiler 1', client='Lean fixture compiler 1'):
        return prepare(self.root, compiler, client)

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


class CachePreparationTests(CacheFixture):
    def build_state(self):
        return {path.relative_to(self.root): (path.read_bytes(), path.stat().st_mtime_ns)
                for package in ('', 'examples/downstream')
                for path in (self.root / package / '.lake/build').rglob('*')
                if path.is_file()}

    def test_compatible_source_and_version_changes_preserve_current_outputs(self):
        self.prepare()
        output = self.artifact('Aglib/Current')
        client = self.artifact('Consumer/Current', 'examples/downstream')
        original = (output.stat().st_mtime_ns, client.stat().st_mtime_ns)
        (self.root / 'Aglib/Current.lean').write_text('module\n-- changed source\n')
        for package in ('', 'examples/downstream'):
            path = self.root / package / 'lakefile.toml'
            path.write_text(path.read_text().replace('0.1.0', '0.2.0'))
        self.assertTrue(all('preserved' in line for line in self.prepare()))
        self.assertEqual((output.stat().st_mtime_ns, client.stat().st_mtime_ns), original)

    def test_compiler_changes_preserve_outputs_and_native_traces_for_rehash(self):
        self.prepare()
        output = self.artifact('Aglib/Current')
        client = self.artifact('Consumer/Current', 'examples/downstream')
        traces = [self.artifact('Aglib/Current', suffix='.trace'),
                  self.artifact('Consumer/Current', 'examples/downstream', suffix='.trace')]
        artifacts = [output, client, *traces]
        original = [(path.read_bytes(), path.stat().st_mtime_ns) for path in artifacts]
        dependency = self.root / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'
        dependency.parent.mkdir(parents=True)
        dependency.write_bytes(b'dependency-owned')
        outside = self.root / 'unrelated'
        outside.write_bytes(b'foreign')
        self.prepare(compiler='Lean fixture compiler 2')
        self.assertEqual([(path.read_bytes(), path.stat().st_mtime_ns) for path in artifacts],
                         original)
        self.assertEqual(dependency.read_bytes(), b'dependency-owned')
        self.assertEqual(outside.read_bytes(), b'foreign')
        self.prepare(compiler='Lean fixture compiler 2', client='Lean fixture compiler 3')
        self.assertEqual([(path.read_bytes(), path.stat().st_mtime_ns) for path in artifacts],
                         original)
        for package, compiler in [('', 'Lean fixture compiler 2'),
                                  ('examples/downstream', 'Lean fixture compiler 3')]:
            self.assertEqual(json.loads((self.root / package / '.lake/build' / STAMP).read_text())[
                'compiler'], compiler)

    def test_abi_compatible_option_and_dependency_changes_preserve_outputs_for_rehash(self):
        self.prepare()
        output = self.artifact('Aglib/Current')
        client = self.artifact('Consumer/Current', 'examples/downstream')
        path = self.root / 'examples/downstream/lakefile.toml'
        path.write_text(path.read_text() + '\n[leanOptions]\nwarningAsError=true\n')
        self.prepare()
        self.assertTrue(output.exists())
        self.assertTrue(client.exists())
        path = self.root / 'lake-manifest.json'
        path.write_text('{"packages": [{"name": "changed-pin"}]}\n')
        self.prepare()
        self.assertTrue(output.exists())
        self.assertTrue(client.exists())
        self.assertEqual(json.loads((self.root / '.lake/build' / STAMP).read_text())[
            'configuration'], config_hash(self.root, ('',)))
        self.assertEqual(json.loads((self.root / 'examples/downstream/.lake/build' / STAMP).read_text())[
            'configuration'], config_hash(self.root))

    def test_toolchain_changes_preserve_outputs_for_native_trace_validation(self):
        self.prepare()
        outputs = [self.artifact('Aglib/Current'),
                   self.artifact('Consumer/Current', 'examples/downstream')]
        original = [(path.read_bytes(), path.stat().st_mtime_ns) for path in outputs]
        for package in ('', 'examples/downstream'):
            with self.subTest(package=package):
                (self.root / package / 'lean-toolchain').write_text('different toolchain\n')
                self.prepare()
                self.assertEqual([(path.read_bytes(), path.stat().st_mtime_ns)
                                  for path in outputs], original)
                self.assertEqual(json.loads((self.root / package / '.lake/build' / STAMP).read_text())[
                    'toolchain'], 'different toolchain\n')

    def test_absent_malformed_and_old_schema_stamps_preserve_native_evidence(self):
        for package, module in [('', 'Aglib/Current'),
                                ('examples/downstream', 'Consumer/Current')]:
            for stamp in (None, '{broken', '[]', json.dumps({'schema': 'old'})):
                with self.subTest(package=package, stamp=stamp):
                    artifacts = [self.artifact(module, package, directory, suffix)
                                 for directory, suffix in [('lib/lean', '.olean'),
                                                           ('lib/lean', '.trace'),
                                                           ('lib/lean', '.olean.hash'),
                                                           ('ir', '.c.o')]]
                    original = [(path.read_bytes(), path.stat().st_mtime_ns)
                                for path in artifacts]
                    metadata = self.root / package / '.lake/build' / STAMP
                    if stamp is None:
                        metadata.unlink(missing_ok=True)
                    else:
                        metadata.write_text(stamp)
                    self.prepare()
                    self.assertEqual([(path.read_bytes(), path.stat().st_mtime_ns)
                                      for path in artifacts], original)
                    self.assertEqual(json.loads(metadata.read_text())['configuration'],
                                     config_hash(self.root, ('',)) if not package
                                     else config_hash(self.root))

    def test_incomplete_stamp_preserves_outputs_without_certifying_them(self):
        self.prepare()
        output = self.artifact('Aglib/Current')
        original = (output.read_bytes(), output.stat().st_mtime_ns)
        metadata = self.root / '.lake/build' / STAMP
        previous = json.loads(metadata.read_text())
        previous.pop('configuration')
        metadata.write_text(json.dumps(previous))
        self.prepare()
        self.assertEqual((output.read_bytes(), output.stat().st_mtime_ns), original)
        # Preparation cannot supply missing native validation evidence. A fresh
        # wrapper stamp alone must never stand in for the subsequent Lake check.
        self.assertFalse(output.with_suffix('.trace').exists())
        self.assertFalse(output.with_suffix('.olean.hash').exists())

    def test_prune_deleted_renamed_and_old_roots_and_all_module_facets(self):
        self.prepare()
        current = []
        for name in ('Aglib', 'Aglib/Current', 'AglibTest', 'AglibTest/Positive',
                     'AglibTest/AuditSupport'):
            current.append(self.artifact(name))
        current.append(self.artifact('Aglib/Current', directory='ir', suffix='.c.o'))
        stale = []
        for name in ('Aglib/Deleted', 'Aglib/Renamed', 'AglibTest/Axioms',
                     'AglibTest/NegativeControls/Bad',
                     'AlgebraicGeometry/Old', 'AlgebraicGeometryTest', 'R5Lab/Old', 'Quillen'):
            for directory, suffix in (('lib/lean', '.olean'), ('lib/lean', '.olean.private'),
                                      ('lib/lean', '.olean.hash'), ('lib/lean', '.trace'),
                                      ('lib/lean', '.ilean'), ('ir', '.c.o')):
                stale.append(self.artifact(name, directory=directory, suffix=suffix))
        stale.append(self.artifact('Consumer/Deleted', 'examples/downstream'))
        client = self.artifact('Consumer/Current', 'examples/downstream')
        self.prepare()
        self.assertTrue(all(path.exists() for path in current + [client]))
        self.assertTrue(all(not path.exists() for path in stale))
        self.assertEqual(check_inventory(self.root), [])

    def test_old_case_roots_are_pruned_without_aliasing_current_enrollment(self):
        # On case-insensitive hosts these names cannot coexist with the current
        # roots; create them first, just as a restored old-root cache would.
        self.prepare()
        stale = [self.artifact('AGLib/Old'), self.artifact('AGLibTest')]
        self.prepare()
        self.assertTrue(all(not path.exists() for path in stale))

    def test_build_root_and_nested_symlinks_fail_without_touching_foreign_paths(self):
        self.prepare()
        output = self.artifact('Aglib/Current')
        foreign = self.root / 'foreign'
        foreign.mkdir()
        protected = foreign / 'protected'
        protected.write_bytes(b'foreign output')
        client_build = self.root / 'examples/downstream/.lake/build'
        import shutil
        shutil.rmtree(client_build)
        client_build.symlink_to(foreign, target_is_directory=True)
        with self.assertRaises(ValueError):
            self.prepare(compiler='changed')
        self.assertTrue(output.exists())  # Validate both roots before any mutation.
        self.assertEqual(protected.read_bytes(), b'foreign output')
        client_build.unlink()
        client_build.mkdir()
        (output.parent / 'Foreign.olean').symlink_to(protected)
        with self.assertRaises(ValueError):
            self.prepare()
        self.assertEqual(protected.read_bytes(), b'foreign output')

    def test_invalid_required_inputs_fail_before_any_build_mutation(self):
        self.prepare()
        for package, module in [('', 'Aglib/Current'),
                                ('examples/downstream', 'Consumer/Current')]:
            self.artifact(module, package)
            self.artifact('Deleted', package)  # Must not be pruned on failure.
        original = self.build_state()
        for compiler, client in [('', 'compiler'), ('compiler', ' \n')]:
            with self.subTest(compiler=compiler, client=client):
                with self.assertRaises(ValueError):
                    self.prepare(compiler=compiler, client=client)
                self.assertEqual(self.build_state(), original)
        for package in ('', 'examples/downstream'):
            for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
                path = self.root / package / name
                previous = path.read_bytes()
                invalid = [None, b' ']
                if name == 'lakefile.toml':
                    invalid += [b'name = [', b'name="fixture"\nvalue=nan\n']
                for content in invalid:
                    with self.subTest(package=package, name=name, content=content):
                        if content is None:
                            path.unlink()
                        else:
                            path.write_bytes(content)
                        with self.assertRaises((OSError, ValueError)):
                            self.prepare(compiler='changed')
                        self.assertEqual(self.build_state(), original)
                        path.write_bytes(previous)


class WorkflowTests(unittest.TestCase):
    def test_python_is_selected_before_source_only_checks(self):
        workflow = (Path(__file__).resolve().parents[1] / '.github/workflows/ci.yml').read_text()
        checkout = workflow.index('uses: actions/checkout@')
        setup = workflow.index('uses: actions/setup-python@5fda3b95a4ea91299a34e894583c3862153e4b97')
        source_only = workflow.index('run: bash scripts/check.sh --source-only')
        self.assertLess(checkout, setup)
        self.assertLess(setup, source_only)
        self.assertIn("python-version: '3.13'", workflow[setup:source_only])

    def test_cache_order_keys_and_unconditional_ci_rehash_route(self):
        workflow = (Path(__file__).resolve().parents[1] / '.github/workflows/ci.yml').read_text()
        compute = workflow.index('id: project-cache-config')
        restore = workflow.index('- name: Restore incremental project builds')
        prepare_step = workflow.index('- name: Validate cached compilers')
        check = workflow.index('- name: Run CI checks for the library and independent client')
        self.assertLess(compute, restore)
        self.assertLess(restore, prepare_step)
        self.assertLess(prepare_step, check)
        cache = workflow[restore:prepare_step]
        self.assertIn('actions/cache/restore@55cc8345863c7cc4c66a329aec7e433d2d1c52a9', cache)
        self.assertIn('            .lake/build\n            examples/downstream/.lake/build\n', cache)
        self.assertIn("hashFiles('Aglib.lean', 'Aglib/**/*.lean'", cache)
        self.assertIn("'!examples/downstream/.lake/**'", cache)
        prefixes = cache.split('restore-keys: |\n', 1)[1].strip().splitlines()
        self.assertEqual([line.strip() for line in prefixes], [
            "project-build-v1-${{ runner.os }}-${{ runner.arch }}-${{ steps.project-cache-config.outputs.hash }}-${{ hashFiles('Aglib.lean', 'Aglib/**/*.lean', 'AglibTest.lean', 'AglibTest/**/*.lean', 'examples/downstream/**/*.lean', '!examples/downstream/.lake/**') }}",
            'project-build-v1-${{ runner.os }}-${{ runner.arch }}-${{ steps.project-cache-config.outputs.hash }}-',
            'project-build-v1-${{ runner.os }}-${{ runner.arch }}-'])
        self.assertNotIn('version', cache)
        save = workflow.index('- name: Save incremental project builds, including partial progress')
        self.assertLess(check, save)
        self.assertNotIn('if:', workflow[check:save])
        self.assertIn('bash scripts/check.sh --rehash --ci', workflow[check:save])
        self.assertIn('LEAN_NUM_THREADS: 1', workflow)
        self.assertIn('scripts/resource_guard.py --bootstrap-cache --receipt '
                      '"$RUNNER_TEMP/mathlib-cache-resource.json" -- lake exe cache get', workflow)

    def test_public_runner_profile_leaves_time_to_save_after_check_timeout(self):
        workflow = (Path(__file__).resolve().parents[1] / '.github/workflows/ci.yml').read_text()
        job = workflow[workflow.index('  library:'):workflow.index('    steps:')]
        self.assertIn('runs-on: ubuntu-24.04', job)
        self.assertIn('timeout-minutes: 360', job)
        self.assertIn('AGLIB_BUILD_THREADS: 4', job)
        self.assertIn('AGLIB_LEAN_MEMORY_MB: 12800', job)
        self.assertIn('AGLIB_RSS_LIMIT_MB: 13824', job)
        environment = {
            name: next(line.strip().split(': ', 1)[1] for line in job.splitlines()
                       if line.strip().startswith(name + ':'))
            for name in ('AGLIB_LEAN_MEMORY_MB', 'AGLIB_RSS_LIMIT_MB')}
        for physical_mib in (16384, 15872):
            profile = limits(environment, physical_mib * 1024**2)
            self.assertEqual(profile['lean_memory_mb'], 12800)
            self.assertEqual(profile['rss_limit_mb'], 13824)
            self.assertEqual(profile['lean_threads'], 1)
            self.assertEqual(profile['max_active_lean'], 1)
        with self.assertRaises(ValueError):
            limits(environment, 15871 * 1024**2)
        check = workflow[workflow.index('- name: Run CI checks for the library and independent client'):]
        self.assertIn('timeout-minutes: 300', check.split('      - name:', 1)[0])
        self.assertIn("cancel-in-progress: ${{ github.ref != 'refs/heads/main' }}", workflow)

    def test_identical_source_retries_advance_immutable_cache_generations(self):
        workflow = (Path(__file__).resolve().parents[1] / '.github/workflows/ci.yml').read_text()
        cache = workflow[workflow.index('- name: Restore incremental project builds'):
                         workflow.index('- name: Validate cached compilers')]
        key = next(line.strip().removeprefix('key: ') for line in cache.splitlines()
                   if line.strip().startswith('key: '))
        prefixes = [line.strip() for line in cache.split('restore-keys: |\n', 1)[1].strip().splitlines()]
        self.assertEqual(key, prefixes[0] + '-${{ github.run_id }}-${{ github.run_attempt }}')
        self.assertTrue(key.startswith(prefixes[1]))
        self.assertTrue(key.startswith(prefixes[2]))
        for prefix in prefixes:
            self.assertNotIn('github.run_id', prefix)
            self.assertNotIn('github.run_attempt', prefix)
        generations = [key.replace('${{ github.run_id }}', run).replace('${{ github.run_attempt }}', attempt)
                       for run, attempt in [('42', '1'), ('42', '2'), ('43', '1')]]
        self.assertEqual(len(set(generations)), 3)
        self.assertTrue(all(generation.startswith(prefixes[0]) for generation in generations))
        # A pre-generation exact-source key is still matched by the first prefix.
        self.assertEqual(prefixes[0], key.rsplit('-${{ github.run_id }}', 1)[0])

    def test_partial_project_save_is_guarded_and_independent_of_check_success(self):
        workflow = (Path(__file__).resolve().parents[1] / '.github/workflows/ci.yml').read_text()
        save = workflow[workflow.index('- name: Save incremental project builds, including partial progress'):]
        condition = next(line.strip() for line in save.splitlines() if line.strip().startswith('if:'))
        self.assertIn('always()', condition)
        self.assertIn("steps.project-build-cache.outputs.cache-primary-key != ''", condition)
        self.assertIn("steps.prepare-project-cache.outcome == 'success'", condition)
        self.assertNotIn('success()', condition)
        self.assertIn('actions/cache/save@55cc8345863c7cc4c66a329aec7e433d2d1c52a9', save)
        self.assertIn('            .lake/build\n            examples/downstream/.lake/build\n', save)
        self.assertIn('key: ${{ steps.project-build-cache.outputs.cache-primary-key }}', save)

    def test_dependency_cache_is_saved_after_fetch_before_long_project_check(self):
        workflow = (Path(__file__).resolve().parents[1] / '.github/workflows/ci.yml').read_text()
        restore = workflow.index('- name: Restore third-party proof cache')
        fetch = workflow.index('- name: Fetch matching Mathlib proof cache')
        save = workflow.index('- name: Save matching third-party proof cache')
        compute = workflow.index('- name: Compute version-independent project cache configuration')
        self.assertLess(restore, fetch)
        self.assertLess(fetch, save)
        self.assertLess(save, compute)
        dependency = workflow[restore:compute]
        self.assertIn('actions/cache/restore@55cc8345863c7cc4c66a329aec7e433d2d1c52a9', dependency)
        self.assertIn('actions/cache/save@55cc8345863c7cc4c66a329aec7e433d2d1c52a9', dependency)
        self.assertIn("key: third-party-${{ runner.os }}-${{ runner.arch }}-${{ hashFiles('lean-toolchain', 'lake-manifest.json') }}", dependency)
        self.assertIn("steps.mathlib-cache-fetch.outcome == 'success'", dependency)
        self.assertIn("steps.third-party-cache.outputs.cache-primary-key != ''", dependency)
        self.assertIn("steps.third-party-cache.outputs.cache-hit != 'true'", dependency)
        self.assertIn('key: ${{ steps.third-party-cache.outputs.cache-primary-key }}', dependency)


if __name__ == '__main__':
    unittest.main()
