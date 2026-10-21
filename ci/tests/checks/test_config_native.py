"""Common native predicates, including opt-in real pinned-runtime fixtures."""
import contextlib
import io
import json
import os
import re
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from lean_ci.checks import native


class NativeInterfaceTests(unittest.TestCase):
    def test_structured_names_and_asset_enrollment(self):
        self.assertEqual(native.module_components('Fixture.«quoted.part».Leaf'),
                         ['Fixture', 'quoted.part', 'Leaf'])
        with self.assertRaises(ValueError):
            native.module_components('../Bad')
        self.assertTrue(all(p.is_file() for p in native.checker_inputs('declarations')))
        self.assertIn('Batteries.Tactic.Lint', native.runtime_roots('declarations'))
        self.assertIn('Lean.Util.CollectAxioms', native.runtime_roots('declarations'))

    def test_cli_forwards_guards_exactly(self):
        with patch('lean_ci.checks.guards.run', return_value=0) as run:
            self.assertEqual(native.main(['source', '--root', '.', '--modules', 'Fixture',
                                          '--config', 'ci.toml']), 0)
        self.assertEqual(run.call_args.args[:1], ('source',))
        self.assertEqual(run.call_args.kwargs['config_path'], Path('ci.toml'))

    def test_source_changed_markdown_paths_are_forwarded(self):
        with patch('lean_ci.checks.guards.run', return_value=0) as run:
            self.assertEqual(native.main(['source', '--root', '.', '--changed-path', 'README.md',
                                          '--changed-path', 'docs/Changed.md']), 0)
        self.assertEqual(run.call_args.kwargs['changed_paths'], ['README.md', 'docs/Changed.md'])

    def test_configured_expected_failure_uses_guard_diagnostic_contract(self):
        with patch('lean_ci.checks.guards.run', return_value=0) as run:
            self.assertEqual(native.main(['expected-failure', '--root', '.', '--modules', 'Negative',
                                          '--config', 'ci.toml']), 0)
        self.assertEqual(run.call_args.args[0], 'expected-failure')

    def test_optional_style_source_runtime_roots(self):
        self.assertEqual(native.runtime_source_roots('style'),
                         ('Cli.Basic', 'ImportGraph.Imports.FromSource'))
        self.assertEqual(native.runtime_source_roots('declarations'), ())

    def test_all_three_origin_batch_kinds_and_cross_kind_rejection(self):
        with tempfile.TemporaryDirectory() as directory:
            selection = Path(directory) / 'selection.json'
            output = Path(directory) / 'results.jsonl'
            for kind in ('declarations', 'axioms', 'inventory'):
                selection.write_text(json.dumps({'schema': 1, 'kind': kind, 'invocation': 'batch',
                    'items': [{'id': 'item', 'module': 'Fixture.Positive',
                               'components': ['Fixture', 'Positive'], 'input_key': 'key'}]}))
                with patch('lean_ci.checks.native.run_origins', return_value=0) as run:
                    self.assertEqual(native.main([kind, '--root', directory, '--selection-json',
                                                  str(selection), '--results-jsonl', str(output)]), 0)
                    self.assertEqual(run.call_args.kwargs['metadata']['kind'], kind)
                other_kind = 'axioms' if kind != 'axioms' else 'inventory'
                with patch('lean_ci.checks.native.run_origins') as run, contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(native.main([other_kind, '--root', directory,
                                                  '--selection-json', str(selection)]), 1)
                    run.assert_not_called()
            metadata = {'kind': 'axioms', 'invocation': 'batch', 'items': {('Fixture', 'Positive'):
                        {'id': 'item', 'module': 'Fixture.Positive', 'input_key': 'key'}}}
            with self.assertRaisesRegex(ValueError, 'kind'):
                native._emit_origin({'kind': 'inventory', 'module': 'Fixture.Positive', 'success': True},
                                    metadata, output)
            self.assertFalse(output.exists())

    def test_nonempty_unsupported_axiom_and_private_generated_data_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            config = Path(directory) / 'ci.toml'
            for kind, key in (('axioms', 'axioms'), ('axioms', 'private_generated'),
                              ('inventory', 'private_generated'), ('controls', 'axioms')):
                config.write_text('[policy]\n' + key + ' = ["unsupported.json"]\n')
                with patch('lean_ci.checks.native.run_origins') as run, patch('lean_ci.checks.guards.run') as guard, contextlib.redirect_stderr(io.StringIO()) as error:
                    self.assertEqual(native.main([kind, '--root', directory, '--modules', 'Fixture',
                                                  '--config', str(config)]), 1)
                    self.assertIn('Unsupported nonempty policy.' + key, error.getvalue())
                    run.assert_not_called()
                    guard.assert_not_called()
            config.write_text('[policy]\naxioms = []\nprivate_generated = []\n')
            with patch('lean_ci.checks.native.run_origins', return_value=0):
                self.assertEqual(native.main(['axioms', '--root', directory, '--modules', 'Fixture',
                                              '--config', str(config)]), 0)

    def test_generated_json_config_nolints_are_git_free_and_repo_relative(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            package = root / 'lean'
            package.mkdir()
            config = root / '.lean-ci/config.json'
            config.parent.mkdir()
            data = root / '.github/nolints.json'
            data.parent.mkdir()
            data.write_text('[["fixtureContext","Foreign.negative"]]')
            config.write_text(json.dumps({'schema': 1, 'package_dir': 'lean',
                                          'policy': {'nolints': ['.github/nolints.json']}}))
            with patch('lean_ci.checks.native.subprocess.run') as run:
                self.assertEqual(native._nolint_paths(package, config), [data.resolve()])
                self.assertEqual(native._nolints(package, config), [['fixtureContext', 'Foreign.negative']])
                native._validate_native_policy('axioms', config)
                run.assert_not_called()
            config.write_text(json.dumps({'schema': 1, 'policy': {'axioms': ['unsupported.json']}}))
            with self.assertRaisesRegex(ValueError, 'Unsupported nonempty policy.axioms'):
                native._validate_native_policy('axioms', config)

    def test_generated_json_config_rejects_duplicate_keys_and_nolint_escape(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'snapshot'
            root.mkdir()
            config = root / '.lean-ci/config.json'
            config.parent.mkdir()
            for text in ('{"schema":1,"schema":1}',
                         '{"schema":1,"policy":{"nolints":[],"nolints":[]}}'):
                config.write_text(text)
                with self.assertRaisesRegex(ValueError, 'Duplicate JSON configuration key'):
                    native._nolint_paths(root, config)
            outside = Path(directory) / 'outside.json'
            outside.write_text('[]')
            config.write_text(json.dumps({'schema': 1, 'policy': {'nolints': ['../outside.json']}}))
            with patch('lean_ci.checks.native.subprocess.run') as run, self.assertRaisesRegex(ValueError, 'escapes'):
                native._nolint_paths(root, config)
            run.assert_not_called()

    def test_native_fixture_prerequisites_can_skip_without_running_lean(self):
        with patch('subprocess.run') as run, self.assertRaisesRegex(unittest.SkipTest, 'LEAN_CI_NATIVE_TEST_ROOT'):
            native_test_configuration({})
        run.assert_not_called()

    def test_native_fixture_configuration_accepts_portable_prepared_root(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            packages = root / '.lake/packages'
            battery = packages / 'batteries/.lake/build/lib/lean/Batteries/Tactic/Lint.olean'
            battery.parent.mkdir(parents=True)
            battery.write_text('fixture artifact')
            style = packages / 'mathlib/scripts/lint-style.lean'
            style.parent.mkdir(parents=True)
            style.write_text('fixture source')
            lean = root / 'toolchain/bin/lean'
            lean.parent.mkdir(parents=True)
            lean.write_text('fixture binary')
            lean.chmod(0o755)
            environment = {'LEAN_CI_NATIVE_TEST_ROOT': str(root),
                           'LEAN_CI_NATIVE_TOOLCHAIN': str(lean.parent.parent)}
            version = subprocess.CompletedProcess([], 0, 'Lean (version 4.34.1, fixture)\n', '')
            with patch('subprocess.run', return_value=version) as run:
                selected, dependencies = native_test_configuration(environment)
                self.assertEqual((selected, dependencies), (lean.resolve(), packages.resolve()))
                run.assert_called_once_with([str(lean.resolve()), '--version'], capture_output=True,
                                             text=True, check=True)
            wrong = subprocess.CompletedProcess([], 0, 'Lean (version 4.35.0)\n', '')
            with patch('subprocess.run', return_value=wrong), self.assertRaisesRegex(AssertionError, 'pinned Lean 4.34.1'):
                native_test_configuration(environment)

    def test_nolints_are_bound_checker_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'scripts/nolints.json'
            path.parent.mkdir()
            path.write_text('[["fixtureContext","Foreign.negative"]]')
            self.assertIn(path, native.checker_inputs('declarations', root))
            self.assertEqual(native._nolints(root), [['fixtureContext', 'Foreign.negative']])

    def test_terminal_sidecar_binds_exact_invocation_and_item(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'results.jsonl'
            metadata = {'invocation': 'one', 'items': {('Fixture', 'Positive'):
                        {'id': 'item', 'module': 'Fixture.Positive', 'input_key': 'input'}}}
            with contextlib.redirect_stdout(io.StringIO()):
                native._emit_origin({'module': 'Fixture.Positive', 'success': True}, metadata, output)
            row = json.loads(output.read_text())
            self.assertEqual((row['invocation'], row['id'], row['input_key'], row['completed']),
                             ('one', 'item', 'input', True))

    def test_missing_dependency_does_not_pass_expected_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'Negative.lean'
            source.write_text('import Missing\n')
            missing = subprocess.CompletedProcess([], 1, "Negative.lean:1:0: error: unknown module prefix 'Missing'", '')
            with patch('lean_ci.checks.native.subprocess.run', return_value=missing), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(native.run_expected_failure(root, [source], {'lean': 'lean'}), 1)


def native_test_configuration(environment=None):
    """Resolve prepared native prerequisites without a platform-specific path."""
    environment = dict(os.environ if environment is None else environment)
    prepared = environment.get('LEAN_CI_NATIVE_TEST_ROOT')
    packages_value = environment.get('LEAN_CI_TEST_PACKAGES')
    if prepared:
        prepared = Path(prepared).resolve()
        packages = prepared / '.lake/packages'
    elif packages_value:
        prepared = None
        packages = Path(packages_value).resolve()
    else:
        raise unittest.SkipTest('native prerequisites missing: set LEAN_CI_NATIVE_TEST_ROOT to a prepared package root')
    if not packages.is_dir():
        raise unittest.SkipTest('native prerequisites missing: prepared .lake/packages tree')
    selected = environment.get('LEAN_CI_NATIVE_TOOLCHAIN') or environment.get('LEAN_CI_TEST_LEAN')
    candidate = Path(selected).expanduser() if selected else None
    if candidate is not None and candidate.is_dir():
        lean = candidate / 'bin/lean'
    elif candidate is not None and candidate.is_file():
        lean = candidate
    else:
        if selected and ('/' in selected and not selected.startswith('leanprover/')):
            raise unittest.SkipTest('native prerequisites missing: selected Lean executable/toolchain path')
        tool_environment = dict(environment, ELAN_TOOLCHAIN=selected or 'leanprover/lean4:v4.34.1')
        try:
            found = subprocess.run(['elan', 'which', 'lean'], cwd=prepared,
                                   env=tool_environment, capture_output=True, text=True)
        except FileNotFoundError:
            raise unittest.SkipTest('native prerequisites missing: elan or explicit LEAN_CI_NATIVE_TOOLCHAIN path')
        if found.returncode:
            raise unittest.SkipTest('native prerequisites missing: installed Lean 4.34.1 toolchain')
        lean = Path(found.stdout.strip())
    if not lean.is_file() or not os.access(lean, os.X_OK):
        raise unittest.SkipTest('native prerequisites missing: executable Lean binary')
    lean = lean.resolve()
    version = subprocess.run([str(lean), '--version'], capture_output=True, text=True, check=True).stdout
    if re.search(r'Lean \(version 4\.34\.1(?:\D|$)', version) is None:
        raise AssertionError('Native fixture requires pinned Lean 4.34.1; observed ' + version.strip())
    if not (packages / 'batteries/.lake/build/lib/lean/Batteries/Tactic/Lint.olean').is_file():
        raise unittest.SkipTest('native prerequisites missing: prepared Batteries.Tactic.Lint native artifact')
    if not (packages / 'mathlib/scripts/lint-style.lean').is_file():
        raise unittest.SkipTest('native prerequisites missing: pinned Mathlib style driver source')
    return lean, packages


class RealNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        lean, cls.packages = native_test_configuration()
        cls.temporary = tempfile.TemporaryDirectory(prefix='native-fixture-', dir=os.environ.get('LEAN_CI_TEST_SCRATCH'))
        cls.root = Path(cls.temporary.name)
        cls.lean = str(lean)
        roots = [str(cls.root)] + [str(p / '.lake/build/lib/lean') for p in sorted(cls.packages.iterdir()) if p.is_dir()]
        cls.environment = {'lean': cls.lean, 'LEAN_PATH': os.pathsep.join(roots),
                           'LEAN_SYSROOT': str(Path(cls.lean).parent.parent),
                           'LEAN_SRC_PATH': os.pathsep.join([str(cls.root)] + [str(p) for p in cls.packages.iterdir() if p.is_dir()])}
        cls.env = dict(os.environ, **{k: v for k, v in cls.environment.items() if k != 'lean'})
        cls.sources = {
            'Fixture/Context.lean': '''module
public meta import Batteries.Tactic.Lint
public meta section
open Lean Batteries.Tactic.Lint
@[env_linter] def fixtureContext : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "isolated"
  errorsFound := "context failure"
  test name := do
    if name == `Foreign.positive && (← getEnv).contains `Foreign.negative then
      return some "another batch origin leaked"
    if name == `Foreign.negative then return some "intentional context negative"
    return none
''',
            'Fixture/Positive.lean': '''module
public import Fixture.Context
@[expose] public section
namespace Foreign
/-- Generated control. -/
inductive Generated where
  | mk : Nat → Generated
private def hidden : Nat := 7
/-- Context positive. -/
def positive : Nat := 1
end Foreign
''',
            'Fixture/Negative.lean': '''import Fixture.Context
namespace Foreign
/-- Context negative. -/
def negative : Nat := 1
end Foreign
''',
            'Fixture/NoLint.lean': '''import Fixture.Context
namespace Foreign
/-- Nolint control. -/
@[nolint fixtureContext] def negative : Nat := 2
end Foreign
'''}
        for relative, text in cls.sources.items():
            source = cls.root / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(text)
            subprocess.run([cls.lean, '-o', str(source.with_suffix('.olean')), relative],
                           cwd=cls.root, env=cls.env, check=True, capture_output=True, text=True)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def capture(self, kind, modules, **kwargs):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = native.run_origins(kind, self.root, [native.module_components(m) for m in modules],
                                        environment=self.environment, **kwargs)
        return status, [json.loads(line) for line in output.getvalue().splitlines()]

    def test_shared_prefix_matches_independent_canonical_imports(self):
        modules = ['Fixture.Positive', 'Fixture.Negative', 'Fixture.NoLint', 'Fixture.Positive']
        status, rows = self.capture('declarations', modules, pilot=True)
        reference_status, reference = self.capture('reference', modules, pilot=True)
        self.assertEqual((status, reference_status), (1, 1))
        self.assertEqual([r['success'] for r in rows], [True, False, True, True])
        self.assertEqual([r['result'] for r in rows], [r['result'] for r in reference])
        for row in rows:
            self.assertGreater(row['prefix_modules'], 0)
            self.assertEqual(row['shared_prefix_modules'], row['prefix_modules'])
            self.assertEqual('Fixture.Negative' in row['environment_modules'], row['module'] == 'Fixture.Negative')
        inventory = rows[0]['result']['inventory']
        self.assertIn('Foreign.Generated.rec', inventory)
        self.assertTrue(any(n.startswith('_private.') and n.endswith('.hidden') for n in inventory))

    def test_external_nolints_and_immediate_bound_sidecar(self):
        scripts = self.root / 'scripts'
        scripts.mkdir(exist_ok=True)
        nolints = scripts / 'nolints.json'
        nolints.write_text('[["fixtureContext","Foreign.negative"]]')
        sidecar = self.root / 'results.jsonl'
        metadata = {'invocation': 'real', 'items': {('Fixture', 'Negative'):
                    {'id': 'negative', 'module': 'Fixture.Negative', 'input_key': 'bound'}}}
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                status = native.run_origins('declarations', self.root, [['Fixture', 'Negative']],
                                            environment=self.environment, metadata=metadata,
                                            results_jsonl=sidecar)
            self.assertEqual(status, 0)
            row = json.loads(sidecar.read_text())
            self.assertTrue(row['completed'] and row['success'])
            self.assertEqual((row['invocation'], row['id'], row['input_key']), ('real', 'negative', 'bound'))
            self.assertEqual(row['result']['diagnostics'], [])
            self.assertIn('fixtureContext', row['result']['checks'])
        finally:
            nolints.unlink()

    def test_shared_native_positive_and_negative_controls(self):
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(native.run_native_controls(self.root, self.environment), 0)

    def test_source_style_without_subject_olean(self):
        (self.root / '.lake').mkdir(exist_ok=True)
        (self.root / '.lake/packages').symlink_to(self.packages, target_is_directory=True)
        (self.root / 'lakefile.toml').write_text('name = "NativeFixture"\n[[lean_lib]]\nname = "StyleOnly"\n')
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
        source = self.root / 'StyleOnly.lean'
        source.write_text('''/-
Copyright (c) 2026 Lean CI contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean CI contributors
-/
module

public import Init

/-! Source-only native style control. -/
''')
        self.assertFalse(source.with_suffix('.olean').exists())
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(native.run_style(self.root, ['StyleOnly'], self.environment), 0)
        self.assertFalse(source.with_suffix('.olean').exists())


if __name__ == '__main__':
    unittest.main()
