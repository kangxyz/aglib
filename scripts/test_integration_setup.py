"""Check isolated downstream setup and exact compiled source replay enrollment."""
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from check_compiled_inventory import check_inventory
from ci_state import ReflectionGraph
from prepare_downstream import manifest_bytes, prepare
from run_style_linter import lake_environment, plan_runtime, run as run_style_linter
import check_negative_controls
import run_declaration_linter


class IntegrationSetupTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='ag-integration-setup-')
        self.root = Path(self.tmp.name)
        (self.root / 'Aglib').mkdir()
        (self.root / 'Aglib.lean').write_text('module\n')
        (self.root / 'Aglib/A.lean').write_text('module\n')

    def tearDown(self):
        self.tmp.cleanup()

    def compiled(self, name):
        path = self.root / '.lake/build/lib/lean' / (name + '.olean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.touch()

    def test_compiled_inventory_requires_every_source(self):
        self.compiled('Aglib')
        self.assertTrue(any('Missing compiled' in error for error in check_inventory(self.root)))
        self.compiled('Aglib/A')
        self.assertEqual(check_inventory(self.root), [])

    def test_selected_inventory_does_not_require_unselected_artifacts(self):
        self.compiled('Aglib/A')
        self.assertEqual(check_inventory(self.root, ['Aglib.A']), [])
        self.assertTrue(check_inventory(self.root))
        self.compiled('Aglib/Deleted')
        self.assertTrue(any('Stale compiled' in error for error in check_inventory(self.root, ['Aglib.A'])))

    def test_compiled_inventory_rejects_deleted_and_negative_sources(self):
        self.compiled('Aglib')
        self.compiled('Aglib/A')
        self.compiled('Aglib/Deleted')
        self.compiled('AglibTest/NegativeControls/ImportedFixture')
        errors = check_inventory(self.root)
        self.assertTrue(any('Stale compiled' in error for error in errors))
        self.assertTrue(any('Negative control' in error for error in errors))

    def test_renamed_basis_rejects_old_prefix_artifacts(self):
        self.compiled('Aglib')
        self.compiled('Aglib/A')
        self.compiled('AlgebraicGeometry/A')
        self.assertTrue(any('Old project-prefix' in error for error in check_inventory(self.root)))

    def test_old_root_case_is_rejected_without_aliasing_the_new_root(self):
        self.compiled('AGLib/A')
        self.assertTrue(any('Old project-prefix compiled artifacts remain: AGLib' in error
                            for error in check_inventory(self.root)))

    def test_client_inherits_pins_and_adds_only_foundation_path(self):
        client = self.root / 'examples/downstream'
        client.mkdir(parents=True)
        packages = self.root / '.lake/packages'
        packages.mkdir(parents=True)
        manifest = {'version': '1.2.0', 'packagesDir': '.lake/packages',
            'name': 'Aglib', 'packages': [
                {'name': 'mathlib', 'rev': 'fixed-mathlib', 'type': 'git', 'inherited': False},
                {'name': 'batteries', 'rev': 'fixed-batteries', 'type': 'git', 'inherited': True}]}
        original = json.dumps(manifest)
        (self.root / 'lake-manifest.json').write_text(original)
        prepare(self.root)
        prepared = json.loads((client / 'lake-manifest.json').read_text())
        self.assertEqual(prepared['name'], '«aglib-downstream»')
        self.assertEqual(prepared['packages'][0]['rev'], 'fixed-mathlib')
        self.assertTrue(all(package['inherited'] for package in prepared['packages'][:-1]))
        self.assertEqual(prepared['packages'][-1]['name'], manifest['name'])
        self.assertEqual(prepared['packages'][-1]['dir'], '../..')
        self.assertEqual((client / '.lake/packages').resolve(), packages.resolve())
        self.assertEqual((self.root / 'lake-manifest.json').read_text(), original)
        before = ReflectionGraph.stamp(client / 'lake-manifest.json')
        link_before = ReflectionGraph.stat_identity((client / '.lake/packages').lstat())
        prepare(self.root)
        self.assertEqual(json.loads((client / 'lake-manifest.json').read_text()), prepared)
        self.assertEqual(ReflectionGraph.stamp(client / 'lake-manifest.json'), before)
        self.assertEqual(ReflectionGraph.stat_identity((client / '.lake/packages').lstat()), link_before)

    def test_client_manifest_bytes_is_pure_and_shared_with_preparation(self):
        client = self.root / 'examples/downstream'
        client.mkdir(parents=True)
        source = self.root / 'lake-manifest.json'
        source.write_text(json.dumps({'name': 'Aglib', 'packages': [
            {'name': 'mathlib', 'rev': 'fixed-pin', 'inherited': False}]}))
        target = client / 'lake-manifest.json'
        target.write_bytes(b'stale tracked downstream metadata\n')
        before = {p.relative_to(self.root): (p.read_bytes(), ReflectionGraph.stamp(p))
                  for p in self.root.rglob('*') if p.is_file()}
        expected = manifest_bytes(self.root)
        self.assertEqual({p.relative_to(self.root): (p.read_bytes(), ReflectionGraph.stamp(p))
                          for p in self.root.rglob('*') if p.is_file()}, before)
        self.assertFalse((client / '.lake').exists())
        self.assertTrue(json.loads(expected)['packages'][0]['inherited'])
        prepare(self.root)
        self.assertEqual(target.read_bytes(), expected)
        stamp = ReflectionGraph.stamp(target)
        self.assertEqual(manifest_bytes(self.root), expected)
        prepare(self.root)
        self.assertEqual(ReflectionGraph.stamp(target), stamp)

    def test_client_preparation_preserves_actual_tracked_manifest_temporal_identity(self):
        source_root = Path(__file__).resolve().parents[1]
        for relative in ('lake-manifest.json', 'examples/downstream/lake-manifest.json'):
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((source_root / relative).read_bytes())
        cache = self.root / '.lake/packages'
        cache.mkdir(parents=True)
        partial = cache / 'keep-partial-progress'
        partial.write_bytes(b'compatible dependency progress')
        tracked = [self.root / p for p in ('lake-manifest.json', 'examples/downstream/lake-manifest.json')]
        before = {p: (p.read_bytes(), ReflectionGraph.stamp(p)) for p in tracked}
        prepare(self.root)
        prepare(self.root)
        self.assertEqual({p: (p.read_bytes(), ReflectionGraph.stamp(p)) for p in tracked}, before)
        link = self.root / 'examples/downstream/.lake/packages'
        self.assertTrue(link.is_symlink())
        self.assertEqual(os.readlink(link), '../../../.lake/packages')
        self.assertEqual(link.resolve(), cache.resolve())
        self.assertEqual(partial.read_bytes(), b'compatible dependency progress')

    def test_client_preparation_updates_changed_pins_but_skips_only_exact_equal_bytes(self):
        client = self.root / 'examples/downstream'
        client.mkdir(parents=True)
        root_manifest = self.root / 'lake-manifest.json'
        root_manifest.write_text(json.dumps({'name': 'Aglib', 'packages': [
            {'name': 'mathlib', 'rev': 'first-pin', 'inherited': False}]}))
        prepare(self.root)
        manifest = client / 'lake-manifest.json'
        original = manifest.read_bytes()
        before = ReflectionGraph.stamp(manifest)
        changed = json.loads(root_manifest.read_text())
        changed['packages'][0]['rev'] = 'repaired-pin'
        root_manifest.write_text(json.dumps(changed))
        prepare(self.root)
        self.assertNotEqual(manifest.read_bytes(), original)
        self.assertNotEqual(ReflectionGraph.stamp(manifest), before)
        self.assertEqual(json.loads(manifest.read_text())['packages'][0]['rev'], 'repaired-pin')
        canonical = manifest.read_bytes()
        # Semantic JSON equality alone must not hide an actual tracked-text rewrite.
        manifest.write_bytes(canonical + b'\n')
        before = ReflectionGraph.stamp(manifest)
        prepare(self.root)
        self.assertEqual(manifest.read_bytes(), canonical)
        self.assertNotEqual(ReflectionGraph.stamp(manifest), before)
        before = ReflectionGraph.stamp(manifest)
        prepare(self.root)
        self.assertEqual(ReflectionGraph.stamp(manifest), before)

    def test_client_preparation_preserves_existing_cache_directory_and_dangling_link(self):
        client = self.root / 'examples/downstream'
        client.mkdir(parents=True)
        (self.root / 'lake-manifest.json').write_text('{"name":"Aglib","packages":[]}\n')
        link = client / '.lake/packages'
        link.parent.mkdir()
        link.mkdir()
        keep = link / 'partial-output'
        keep.write_bytes(b'owned existing cache')
        prepare(self.root)
        self.assertFalse(link.is_symlink())
        self.assertEqual(keep.read_bytes(), b'owned existing cache')
        keep.unlink()
        link.rmdir()
        link.symlink_to('existing-missing-target', target_is_directory=True)
        before = ReflectionGraph.stat_identity(link.lstat())
        prepare(self.root)
        self.assertEqual(os.readlink(link), 'existing-missing-target')
        self.assertEqual(ReflectionGraph.stat_identity(link.lstat()), before)

    def test_optional_linter_dependencies_are_planned_without_cache_writes(self):
        driver = self.root / '.lake/packages/mathlib/scripts/lint-style.lean'
        driver.parent.mkdir(parents=True)
        driver.write_text('import Cli.Basic\nimport ImportGraph.Imports.FromSource\n')
        for package, module, imported in [
            ('Cli', 'Cli/Basic.lean', 'Std.Data.TreeSet'),
            ('importGraph', 'ImportGraph/Imports/FromSource.lean', 'Lean.Elab.ParseImportsFast')]:
            source = self.root / '.lake/packages' / package / module
            source.parent.mkdir(parents=True)
            source.write_text('module\npublic import ' + imported + '\n')
        sysroot = self.root / 'toolchain'
        for module in ['Std/Data/TreeSet.olean', 'Lean/Elab/ParseImportsFast.olean']:
            artifact = sysroot / 'lib/lean' / module
            artifact.parent.mkdir(parents=True)
            artifact.touch()
        (sysroot / 'lib/lean/libLake_shared.dylib').touch()
        before = sorted(str(path) for path in self.root.rglob('*'))
        plan = plan_runtime(self.root, sysroot)
        self.assertEqual(plan['missing_prerequisites'], [])
        self.assertEqual({entry['module'] for entry in plan['isolated_compile_modules']},
                         {'Cli.Basic', 'ImportGraph.Imports.FromSource'})
        self.assertEqual(sorted(str(path) for path in self.root.rglob('*')), before)
        (sysroot / 'lib/lean/Std/Data/TreeSet.olean').unlink()
        self.assertIn('Std.Data.TreeSet (optional-source prerequisite)',
                      plan_runtime(self.root, sysroot)['missing_prerequisites'])

    def test_style_environment_prefers_explicit_cap_over_lake_path_and_keeps_fallback(self):
        binary = self.root / 'bin'
        binary.mkdir()
        lake = binary / 'lake'
        lake.write_text('#!/usr/bin/env python3\nimport os,sys\n'
                        'assert sys.argv[1:3] == ["env", "python3"]\n'
                        'os.environ["LEAN"] = os.environ["NATIVE_TEST_LEAN"]\n'
                        'os.execv(sys.executable, [sys.executable, *sys.argv[3:]])\n')
        lake.chmod(0o755)
        uncapped = binary / 'lean'
        uncapped.write_text('#!/usr/bin/env python3\nraise SystemExit(97)\n')
        uncapped.chmod(0o755)
        capped = self.root / 'explicit-capped-lean'
        capped.write_text('#!/usr/bin/env python3\nraise SystemExit(98)\n')
        capped.chmod(0o755)
        for explicit in [str(capped), '']:
            with self.subTest(explicit_cap=bool(explicit)), patch.dict(os.environ, {
                    'PATH': str(binary) + os.pathsep + os.environ.get('PATH', ''),
                    'LEAN': explicit, 'LEAN_PATH': '/fixed/modules',
                    'NATIVE_TEST_LEAN': str(uncapped),
                    'LEAN_SRC_PATH': '/fixed/sources'}):
                environment = lake_environment(self.root)
            self.assertEqual(environment['lean'], explicit or str(uncapped))
            self.assertEqual(environment['LEAN_PATH'], '/fixed/modules')
            self.assertEqual(environment['LEAN_SRC_PATH'], '/fixed/sources')

    def test_declaration_launcher_preserves_explicit_outer_lean_wrapper(self):
        import subprocess
        driver = self.root / run_declaration_linter.DRIVER
        driver.parent.mkdir(parents=True)
        driver.write_text(run_declaration_linter.MARKER)
        for explicit in ['/owned/capped/bin/lean', '']:
            with self.subTest(explicit=explicit), patch.dict(os.environ, {'LEAN': explicit}), \
                    patch.object(run_declaration_linter.subprocess, 'run',
                                 return_value=subprocess.CompletedProcess([], 0)) as process:
                self.assertEqual(run_declaration_linter.run(self.root, ['Aglib.Selected']), 0)
                self.assertEqual(process.call_args.args[0][:4],
                                 ['lake', 'env', explicit or 'lean', '--run'])

    def test_style_runtime_writes_only_temporary_optional_outputs_and_propagates_failure(self):
        import subprocess
        driver = self.root / '.lake/packages/mathlib/scripts/lint-style.lean'
        driver.parent.mkdir(parents=True)
        driver.write_text('import Cli.Basic\n')
        package = self.root / '.lake/packages/Cli'
        source = package / 'Cli/Basic.lean'
        source.parent.mkdir(parents=True)
        source.write_text('module\npublic import Std.Data.TreeSet\n')
        sibling = package / '.lake/build/lib/lean/Cli/Sibling.olean'
        sibling.parent.mkdir(parents=True)
        sibling.write_bytes(b'immutable cached sibling')
        sibling_ir = sibling.with_suffix('.ir')
        sibling_ir.write_bytes(b'immutable cached runtime')
        sysroot = self.root / 'toolchain'
        cached = sysroot / 'lib/lean/Std/Data/TreeSet.olean'
        cached.parent.mkdir(parents=True)
        cached.touch()
        shared = sysroot / 'lib/lean/libLake_shared.dylib'
        shared.touch()
        calls = []
        def process(argv, **kwargs):
            calls.append((argv, kwargs))
            if argv[1:] == ['--print-prefix']:
                return subprocess.CompletedProcess(argv, 0, str(sysroot) + '\n', '')
            if argv[1] == '-o':
                output = Path(argv[2])
                self.assertNotIn('.lake/packages', output.as_posix())
                self.assertNotIn('.lake/build', output.as_posix())
                if output.name == 'AglibStyleDriver.olean':
                    self.assertEqual(kwargs['cwd'], output.parent)
                    self.assertEqual((output.parent / argv[3]).read_bytes(), driver.read_bytes())
                    return subprocess.CompletedProcess(argv, 0)
                self.assertEqual(kwargs['cwd'], str(package))
                self.assertTrue(kwargs['env']['LEAN_PATH'].startswith(str(output.parents[1])))
                for artifact in [sibling, sibling_ir]:
                    linked = output.parent / artifact.name
                    self.assertTrue(linked.is_symlink())
                    self.assertEqual(linked.resolve(), artifact.resolve())
                self.assertFalse(output.is_symlink())
                return subprocess.CompletedProcess(argv, 0)
            self.assertEqual(argv[1:4], ['--load-dynlib', str(shared), '--run'])
            self.assertEqual(argv[-2:], ['Aglib', 'AglibTest'])
            self.assertEqual(Path(argv[4]).read_text(), 'import AglibStyleDriver\n')
            return subprocess.CompletedProcess(argv, 19)
        environment = {'lean': '/pinned/toolchain/bin/lean', 'LEAN_PATH': '/cached/modules',
                       'LEAN_SRC_PATH': '/pinned/sources'}
        with patch('run_style_linter.lake_environment', return_value=environment), \
                patch('run_style_linter.subprocess.run', side_effect=process):
            self.assertEqual(run_style_linter(self.root), 19)
        self.assertEqual(len(calls), 4)
        self.assertEqual(sibling.read_bytes(), b'immutable cached sibling')
        self.assertEqual(sibling_ir.read_bytes(), b'immutable cached runtime')
        self.assertFalse((sibling.parent / 'Basic.olean').exists())

    def test_negative_overlay_retains_positive_artifacts_and_requires_specific_rejection(self):
        from contextlib import redirect_stderr, redirect_stdout
        import io
        import subprocess
        positive = self.root / '.lake/build/lib/lean/AglibTest/AuditSupport.olean'
        positive.parent.mkdir(parents=True)
        positive.write_bytes(b'positive audit support')
        excluded = positive.parent / 'NegativeControls/Old.olean'
        excluded.parent.mkdir()
        excluded.write_bytes(b'excluded control')
        def process(argv, **kwargs):
            if argv[:2] == ['lake', 'env']:
                return subprocess.CompletedProcess(argv, 0, '/cached/modules\n', '')
            overlay = Path(kwargs['env']['LEAN_PATH'].split(':')[0])
            linked = overlay / 'AglibTest/AuditSupport.olean'
            self.assertTrue(linked.is_symlink())
            self.assertEqual(linked.resolve(), positive.resolve())
            self.assertFalse((overlay / 'AglibTest/NegativeControls/Old.olean').exists())
            if '-o' in argv:
                self.assertFalse(Path(argv[argv.index('-o') + 1]).is_symlink())
                return subprocess.CompletedProcess(argv, 0)
            name = 'importedBad' if argv[-1].endswith('ImportedAudit.lean') else 'localBad'
            diagnostic = 'depends on unsupported assumption ' + name if reject else 'missing olean'
            return subprocess.CompletedProcess(argv, 1, diagnostic, '')
        with patch.object(check_negative_controls, 'ROOT', self.root), \
                patch('check_negative_controls.subprocess.run', side_effect=process), \
                redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            reject = True
            self.assertEqual(check_negative_controls.main(), 0)
            reject = False
            self.assertEqual(check_negative_controls.main(), 1)
        self.assertEqual(positive.read_bytes(), b'positive audit support')

    def test_maintained_scripts_match_exact_documentation_mentions(self):
        scripts = Path(__file__).parent
        readme = (scripts / 'README.md').read_text()
        undocumented = [path.name for path in scripts.iterdir()
                        if path.name not in {'README.md', 'bench', 'noshake.json', 'nolints-style.txt'}
                        and f'`{path.name}`' not in readme]
        self.assertEqual(undocumented, [])


if __name__ == '__main__':
    unittest.main()
