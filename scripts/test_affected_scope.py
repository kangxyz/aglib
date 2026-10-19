"""Small Git/import fixtures and mocked native commands; never invoke Lean."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from affected_scope import cache_roots, select, validate
from check_affected import execute
from run_style_linter import selected_driver
from run_declaration_linter import (MARKER, run as run_selected_declaration_linter,
                                    selected_driver as selected_declaration_driver)
from ci_audit import AUDIT_DRIVER


class AffectedScopeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='aglib-scope-fixture-')
        self.root = Path(self.temp.name) / 'repo'
        self.root.mkdir()
        self.write('Aglib/Base.lean', 'module\ndef base := 1\n')
        self.write('Aglib/Dep.lean', 'module\npublic import Aglib.Base\ndef dependent := 1\n')
        self.write('Aglib/Cold.lean', 'module\ndef cold := 1\n')
        self.write('Aglib.lean', 'module\npublic import Aglib.Dep\npublic import Aglib.Cold\n')
        self.write('AglibTest/Focused.lean', 'import Aglib.Dep\nexample : True := trivial\n')
        self.write('AglibTest.lean', 'import AglibTest.Focused\n')
        self.write('AglibTest/AuditSupport.lean', 'import Lean\ndef support := 1\n')
        self.write('AglibTest/Axioms.lean',
                   (Path(__file__).resolve().parents[1] / 'AglibTest/Axioms.lean').read_text())
        self.write('AglibTest/AuditCoverage.lean', 'module\ndef coverage := 1\n')
        self.write('examples/downstream/Consumer/Use.lean', 'module\npublic import Aglib.Dep\ndef use := 1\n')
        self.write('examples/downstream/Consumer.lean', 'module\npublic import Consumer.Use\n')
        self.write('examples/downstream/Audit.lean', 'import Consumer\n')
        self.write('README.md', 'Fixture.\n')
        self.write('scripts/README.md', 'Fixture scripts.\n')
        self.write('docs/evidence.json', '{}\n')
        self.write(AUDIT_DRIVER, (Path(__file__).resolve().parents[1] / AUDIT_DRIVER).read_text())
        self.write('lean-toolchain', 'fixed\n')
        self.write('lakefile.toml', 'name = "Aglib"\n')
        self.write('lake-manifest.json', '{"packages": []}\n')
        self.write('.gitignore', '.lake/\n')
        self.write('.lake/packages/batteries/scripts/runLinter.lean', 'import Batteries.Tactic.Lint\nimport Lake.CLI.Main\n')
        self.write('.lake/packages/mathlib/scripts/lint-style.lean', 'import Mathlib.Tactic.Linter.TextBased\nimport Cli.Basic\n')
        self.git('init', '-q')
        self.git('add', '.')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'fixed fixture')
        self.base = self.git('rev-parse', 'HEAD').strip()

    def tearDown(self):
        self.temp.cleanup()

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True)

    def changed_plan(self):
        self.write('Aglib/Base.lean', 'module\ndef base := 2\n')
        return select(self.root, self.base)

    def test_actual_affected_graph_keeps_consumers_without_cold_siblings(self):
        plan = self.changed_plan()
        self.assertEqual(plan['providers'], ['Aglib.Base'])
        self.assertEqual(plan['consumers'], ['Aglib', 'Aglib.Dep'])
        self.assertEqual(plan['tests'], ['AglibTest', 'AglibTest.Focused'])
        self.assertEqual(plan['client'], ['Consumer', 'Consumer.Use'])
        self.assertNotIn('Aglib.Cold', plan['providers'] + plan['consumers'])
        self.assertNotIn('AglibTest.Axioms', plan['tests'])
        self.assertIn('Aglib.Cold', plan['imports']['Aglib'])
        self.assertEqual(plan['style'], ['Aglib.Base'])
        self.assertEqual(plan['coverage'], 'affected-only')

    def test_changed_facade_is_compiled_consumer(self):
        self.write('Aglib.lean', 'module\npublic import Aglib.Dep\n')
        plan = select(self.root, self.base)
        self.assertEqual(plan['consumers'], ['Aglib'])
        self.assertEqual(plan['providers'], [])
        self.assertTrue(plan['native'])

    def test_ci_lean_files_select_native_tooling_without_production_enrollment(self):
        for path in ('ci/lean/SelectedAudit.lean', 'ci/fixtures/quartz/Check.lean'):
            with self.subTest(path=path):
                self.write(path, 'import Lean\n')
                plan = select(self.root, self.base)
                self.assertTrue(plan['native'] and plan['trust'] and plan['controls'])
                self.assertIn('lean-ci', plan['tooling_tests'])
                self.assertEqual(plan['providers'] + plan['consumers'] + plan['tests'], [])

    def test_deleted_ci_lean_file_remains_a_native_tooling_change(self):
        path = 'ci/fixtures/quartz/Check.lean'
        self.write(path, 'import Aglib.Base\n')
        self.git('add', '--', path)
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'fixed CI fixture')
        base = self.git('rev-parse', 'HEAD').strip()
        (self.root / path).unlink()
        plan = select(self.root, base)
        self.assertTrue(plan['native'] and plan['controls'])
        self.assertEqual(plan['providers'] + plan['consumers'] + plan['tests'], [])

    def test_verified_base_keeps_proof_changes_after_later_tooling_commit(self):
        self.write('Aglib/Base.lean', 'module\ndef base := 2\n')
        self.git('add', 'Aglib/Base.lean')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'proof with unfinished CI')
        previous_push = self.git('rev-parse', 'HEAD').strip()
        self.write('scripts/cache_ci.py', '# repair tooling after failed proof CI\n')
        self.git('add', 'scripts/cache_ci.py')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'tooling repair')
        pending = select(self.root, self.base, head='HEAD')
        self.assertIn('Aglib.Base', pending['providers'])
        self.assertTrue(pending['native'])
        self.assertTrue(pending['trust'])
        self.assertIn('AglibTest.Focused', pending['tests'])
        self.assertFalse(select(self.root, previous_push, head='HEAD')['native'])

    def test_deleted_and_renamed_provider_retain_old_dependents(self):
        (self.root / 'Aglib/Base.lean').rename(self.root / 'Aglib/New.lean')
        plan = select(self.root, self.base)
        self.assertEqual(plan['providers'], ['Aglib.New'])
        self.assertIn('Aglib.Dep', plan['consumers'])
        self.assertIn('Aglib/Base.lean', plan['changed'])
        self.assertIn('Aglib/New.lean', plan['changed'])

    def test_docs_and_evidence_json_run_only_static_checks(self):
        self.write('README.md', '[evidence](docs/evidence.json)\n')
        self.write('docs/evidence.json', '{"status": "partial"}\n')
        self.write('scripts/README.md', 'Changed script documentation.\n')
        plan = select(self.root, self.base)
        self.assertFalse(plan['native'])
        self.assertEqual(plan['tooling_tests'], [])
        calls = []
        output = Path(self.temp.name) / 'no-export.jsonl'
        with patch('check_affected.run', side_effect=lambda root, cmd: calls.append(cmd)):
            execute(self.root, plan, None, outputs=output)
        self.assertEqual(len(calls), 4)
        self.assertFalse(output.exists())
        self.assertFalse(any('lake' in list(map(str, cmd)) for cmd in calls))
        self.assertEqual(plan['cache_imports'], [])
        self.assertEqual(cache_roots(self.root, plan), [])

    def test_cache_projection_follows_actual_local_client_trust_and_tooling_imports(self):
        self.write('Aglib/Base.lean', 'module\npublic import Mathlib.Provider\ndef base := 1\n')
        self.write('Aglib/Cold.lean', 'module\npublic import Mathlib.FacadeDependency\ndef cold := 1\n')
        self.write('examples/downstream/Consumer/Use.lean',
                   'import Aglib.Dep\nimport Mathlib.Client\ndef use := 1\n')
        self.write('AglibTest/AuditCoverage.lean', 'import Mathlib.Trust\n')
        self.write('AglibTest/NegativeControls/ImportedAudit.lean',
                   'import AglibTest.AuditSupport\nimport Mathlib.Trust\n\n'
                   'run_cmd do\n  let count ← IO.pure 0\n')
        self.write('.lake/packages/batteries/Batteries/Tactic/Lint.lean', 'import Mathlib.ToolDependency\n')
        self.write('.lake/packages/Cli/Cli/Basic.lean', 'import Init\n')
        for name in ('Provider', 'FacadeDependency', 'Client', 'Trust', 'ToolDependency',
                     'Tactic/Linter/TextBased'):
            self.write('.lake/packages/mathlib/Mathlib/' + name + '.lean', 'import Init\n')
        self.write('.lake/packages/mathlib/Mathlib/Unrelated.lean', 'import Init\n')
        plan = select(self.root, self.base)
        self.assertTrue(plan['controls'])
        self.assertEqual(cache_roots(self.root, plan),
                         ['Mathlib.Client', 'Mathlib.FacadeDependency', 'Mathlib.Provider',
                          'Mathlib.Tactic.Linter.TextBased', 'Mathlib.ToolDependency', 'Mathlib.Trust'])
        self.assertNotIn('Mathlib.Unrelated', plan['cache_imports'])
        # The selected Aglib facade really imports Cold; its cache basis stays present.
        self.assertIn('Mathlib.FacadeDependency', plan['cache_imports'])

    def test_cache_projection_rejects_missing_pinned_tooling_without_default_fetch(self):
        plan = self.changed_plan()
        (self.root / '.lake/packages/mathlib/scripts/lint-style.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing pinned linter source'):
            cache_roots(self.root, plan)

    def test_tooling_selects_its_affected_fixture_tests_without_lean(self):
        self.write('scripts/affected_scope.py', '# changed selector fixture\n')
        plan = select(self.root, self.base)
        self.assertFalse(plan['native'])
        self.assertEqual(plan['tooling_tests'], ['test_affected_scope'])

    def test_new_tooling_paths_require_explicit_regression_selection(self):
        for path in ('scripts/new_helper.py', 'scripts/nested/check_kernel.py'):
            with self.subTest(path=path):
                self.write(path, '# unassigned helper\n')
                with self.assertRaisesRegex(ValueError, 'assign its regression scope explicitly'):
                    select(self.root, self.base)
                (self.root / path).unlink()

    def test_missing_base_unknown_path_and_pin_fail_closed(self):
        with self.assertRaises(ValueError):
            select(self.root)
        with self.assertRaises(subprocess.CalledProcessError):
            select(self.root, 'missing-base')
        self.write('unknown.toml', 'unknown = true\n')
        with self.assertRaisesRegex(ValueError, 'Unrecognized changed path'):
            select(self.root, self.base)
        (self.root / 'unknown.toml').unlink()
        self.write('lean-toolchain', 'another pin\n')
        with self.assertRaisesRegex(ValueError, 'Configuration/pin'):
            select(self.root, self.base)

    def test_zero_before_uses_true_initial_diff_or_available_merge_base(self):
        initial = select(self.root, '0' * 40, head='HEAD')
        self.assertIn('Aglib.Base', initial['providers'])
        self.assertNotEqual(initial['base'], self.base)
        self.write('Aglib/Base.lean', 'module\ndef base := 2\n')
        self.git('add', 'Aglib/Base.lean')
        self.git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                 'commit', '-qm', 'branch fixture')
        selected = select(self.root, '0' * 40, head='HEAD', default_base=self.base)
        self.assertEqual(selected['base'], self.base)
        self.assertEqual(selected['providers'], ['Aglib.Base'])
        with self.assertRaisesRegex(ValueError, 'New-branch event'):
            select(self.root, '0' * 40, head='HEAD')

    def test_new_unselected_change_invalidates_plan(self):
        plan = self.changed_plan()
        self.write('Aglib/Cold.lean', 'module\ndef changedCold := 1\n')
        with self.assertRaisesRegex(ValueError, 'scope drifted'):
            validate(self.root, plan)

    def test_selected_input_drift_rejects_plan(self):
        plan = self.changed_plan()
        self.write('Aglib/Dep.lean', 'module\ndef changed := 1\n')
        with self.assertRaisesRegex(ValueError, 'Plan input changed'):
            validate(self.root, plan)

    def native_mock(self, calls, failure=None):
        def command(root, args):
            args = list(map(str, args))
            calls.append(args)
            if failure and any(failure in a for a in args):
                raise subprocess.CalledProcessError(19, args)
            if 'scripts/build_serial.py' in ' '.join(args) and '--outputs' in args:
                index = args.index('--outputs')
                path = Path(args[index + 1])
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(json.dumps({'checked_targets': args[index + 2:]}) + '\n')
        return command

    def test_providers_linted_before_consumers_and_export_reuses_actual_mappings(self):
        plan, calls = self.changed_plan(), []
        directory = Path(self.temp.name) / 'run'
        output = directory / 'selected.jsonl'
        with patch('check_affected.run', side_effect=self.native_mock(calls)):
            execute(self.root, plan, directory, native_only=True, ci=True, outputs=output)
        text = [' '.join(command) for command in calls]
        compile_provider = next(i for i, cmd in enumerate(text) if 'build_serial.py' in cmd and '/providers ' in cmd)
        provider_lint = next(i for i, cmd in enumerate(text) if 'providers-declarations' in cmd)
        provider_style = next(i for i, cmd in enumerate(text) if 'providers-style' in cmd)
        heavy = next(i for i, cmd in enumerate(text) if 'build_serial.py' in cmd and '/consumers ' in cmd)
        self.assertLess(compile_provider, provider_lint)
        self.assertLess(provider_lint, provider_style)
        self.assertLess(provider_style, heavy)
        self.assertTrue(any('--no-build lint --builtin-only Aglib.Base' in cmd for cmd in text))
        consumer_lint = next(i for i, cmd in enumerate(text) if 'consumers-declarations' in cmd)
        test_compile = next(i for i, cmd in enumerate(text) if 'build_serial.py' in cmd and '/tests ' in cmd)
        self.assertLess(test_compile, consumer_lint)
        self.assertIn('run_declaration_linter.py Aglib.Dep AglibTest.Focused', text[consumer_lint])
        self.assertNotIn('Aglib.Base', text[consumer_lint])
        self.assertNotIn('Aglib.Cold', text[consumer_lint])
        self.assertFalse(any('consumers-style' in cmd for cmd in text))
        guard = next(cmd for cmd in text if 'consumers-cached-imports' in cmd)
        self.assertIn('--no-build build Aglib.Cold', guard)
        exported = [json.loads(line)['checked_targets'] for line in output.read_text().splitlines()]
        self.assertEqual(exported, [plan['providers'], plan['consumers'], plan['tests'],
                                    ['AglibTest.AuditSupport', 'AglibTest.AuditCoverage']])
        self.assertFalse(any('native-cache-export' in cmd for cmd in text))
        coverage = json.loads(output.with_suffix('.jsonl.coverage.json').read_text())
        self.assertEqual(coverage['coverage'], 'affected-only')
        self.assertNotIn('Aglib.Cold', coverage['selected_targets'])

    def test_provider_lint_failure_stops_heavy_work_and_export(self):
        plan, calls = self.changed_plan(), []
        directory = Path(self.temp.name) / 'run'
        output = directory / 'selected.jsonl'
        with patch('check_affected.run', side_effect=self.native_mock(calls, 'providers-declarations')):
            with self.assertRaises(subprocess.CalledProcessError):
                execute(self.root, plan, directory, native_only=True, ci=True, outputs=output)
        self.assertFalse(output.exists())
        self.assertFalse(any('/consumers' in ' '.join(c) for c in calls))

    def test_builtin_lint_isolates_exact_modules_with_distinct_guard_receipts(self):
        self.write('Aglib/Cold.lean', 'module\ndef cold := 2\n')
        plan, calls = self.changed_plan(), []
        directory = Path(self.temp.name) / 'run'
        with patch('check_affected.run', side_effect=self.native_mock(calls)):
            execute(self.root, plan, directory, native_only=True, rehash=True,
                    ci=True, phases=['provider-lint'])
        builtin = [c for c in calls if '--builtin-only' in c]
        self.assertEqual(plan['providers'], ['Aglib.Base', 'Aglib.Cold'])
        self.assertEqual(len(builtin), 2)
        for index, (command, module) in enumerate(zip(builtin, plan['providers']), 1):
            self.assertEqual(command[:4], ['python3', str(self.root / 'scripts/resource_guard.py'),
                                          '--capped-toolchain', '--receipt'])
            self.assertEqual(command[4], str(directory / f'providers-builtin-{index:04d}.json'))
            self.assertEqual(command[5:], ['--', 'lake', '--rehash', '--no-build',
                                           'lint', '--builtin-only', module])
        declarations = next(i for i, c in enumerate(calls) if 'scripts/run_declaration_linter.py' in c)
        self.assertGreater(declarations, max(calls.index(c) for c in builtin))
        self.assertEqual(calls[declarations][-2:], plan['providers'])

    def test_builtin_lint_failure_stops_remaining_modules_and_lint_categories(self):
        self.write('Aglib/Cold.lean', 'module\ndef cold := 2\n')
        self.write('Aglib/Dep.lean', 'module\npublic import Aglib.Base\ndef dependent := 2\n')
        plan, calls = self.changed_plan(), []
        with patch('check_affected.run',
                   side_effect=self.native_mock(calls, 'providers-builtin-0002.json')):
            with self.assertRaises(subprocess.CalledProcessError) as failure:
                execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True,
                        ci=True, phases=['provider-lint'])
        self.assertEqual(failure.exception.returncode, 19)
        self.assertEqual(plan['providers'], ['Aglib.Base', 'Aglib.Cold', 'Aglib.Dep'])
        self.assertEqual([c[-1] for c in calls if '--builtin-only' in c], plan['providers'][:2])
        self.assertFalse(any('scripts/run_declaration_linter.py' in c for c in calls))
        self.assertFalse(any('scripts/run_style_linter.py' in c for c in calls))

    def test_cold_facade_import_fails_without_build_fallback(self):
        plan, calls = self.changed_plan(), []
        with patch('check_affected.run', side_effect=self.native_mock(calls, 'consumers-cached-imports')):
            with self.assertRaises(subprocess.CalledProcessError):
                execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True, ci=True)
        self.assertFalse(any('build_serial.py' in ' '.join(c) and '/consumers ' in ' '.join(c) for c in calls))

    def test_single_phase_repair_does_not_repeat_provider_checks(self):
        plan, calls = self.changed_plan(), []
        with patch('check_affected.run', side_effect=self.native_mock(calls)):
            execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True,
                    ci=True, phases=['provider-lint'])
        self.assertEqual(len(calls), 4)
        self.assertTrue(all('providers-' in ' '.join(c) for c in calls))

    def test_style_adapter_preserves_checks_options_and_exact_module_enumeration(self):
        source = ('options\n  -- Get all the imports, but only those in the same package.\n'
                  '  let allModuleNames ← originModules.flatMapM expandImports\n'
                  '  -- Read the `nolints` file\n'
                  '  lintModules opts nolints allModuleNames\n  undocumentedScripts opts\n')
        selected = selected_driver(source)
        self.assertIn('let allModuleNames := originModules', selected)
        self.assertIn('lintModules opts nolints allModuleNames', selected)
        self.assertIn('undocumentedScripts opts', selected)
        with self.assertRaises(ValueError):
            selected_driver('unexpected driver revision')

    def test_declaration_adapter_keeps_enabled_checks_and_exact_module_filter(self):
        source = ('preamble\n' + MARKER
                  + '    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)\n'
                  + '    let results ← lintCore decls linters\n'
                  + '    if failed then IO.Process.exit 1\n')
        selected = selected_declaration_driver(source)
        self.assertIn('lintEnv.getModuleIdxFor? name', selected)
        self.assertIn('lintEnv.header.moduleNames[index.toNat]! == module', selected)
        self.assertIn('getChecks (slow := true) (runAlways := none) (runOnly := none)', selected)
        self.assertIn('lintCore decls linters', selected)
        self.assertIn('if failed then IO.Process.exit 1', selected)
        with self.assertRaises(ValueError):
            selected_declaration_driver('unrecognized driver')

    def test_declaration_lint_runs_each_exact_origin_sequentially(self):
        source = 'preamble\n' + MARKER + '    let linters ← getChecks\n'
        self.write('.lake/packages/batteries/scripts/runLinter.lean', source)
        modules = ['Aglib.Dep', 'Aglib.Base']
        calls = []

        def command(args, cwd):
            self.assertEqual(cwd, self.root)
            self.assertEqual(args[:4], ['lake', 'env', 'fixture-lean', '--run'])
            self.assertEqual(Path(args[4]).read_text(), selected_declaration_driver(source))
            self.assertEqual(args[5:], ['--no-build', modules[len(calls)]])
            calls.append(args)
            return subprocess.CompletedProcess(args, 0)

        with patch.dict(os.environ, {'LEAN': 'fixture-lean'}), \
                patch('run_declaration_linter.subprocess.run', side_effect=command):
            self.assertEqual(run_selected_declaration_linter(self.root, modules), 0)
        self.assertEqual(len(calls), len(modules))
        self.assertEqual(calls[0][4], calls[1][4])
        self.assertFalse(Path(calls[0][4]).exists())

    def test_declaration_lint_failure_stops_at_first_failed_origin(self):
        self.write('.lake/packages/batteries/scripts/runLinter.lean', 'preamble\n' + MARKER)
        modules = ['Aglib.Base', 'Aglib.Dep', 'Aglib.Cold']
        for failed_index in (0, 1):
            with self.subTest(failed_index=failed_index):
                calls = []

                def command(args, cwd):
                    calls.append(args)
                    return subprocess.CompletedProcess(args, 19 if len(calls) > failed_index else 0)

                with patch('run_declaration_linter.subprocess.run', side_effect=command):
                    self.assertEqual(run_selected_declaration_linter(self.root, modules), 19)
                self.assertEqual([c[5:] for c in calls],
                                 [['--no-build', module] for module in modules[:failed_index + 1]])

    def test_client_only_changes_have_no_root_publication(self):
        self.write('examples/downstream/Consumer/Use.lean',
                   'module\npublic import Aglib.Dep\ndef use := 2\n')
        plan = select(self.root, self.base)
        self.assertTrue(plan['native'])
        self.assertFalse(plan['publish'])
        self.assertFalse(plan['trust'])

    def test_changed_audit_support_retains_origin_audit_without_automatic_kernel_replay(self):
        self.write('AglibTest/AuditSupport.lean', 'import Lean\ndef support := 2\n')
        plan, calls = select(self.root, self.base), []
        directory = Path(self.temp.name) / 'run'
        with patch('check_affected.run', side_effect=self.native_mock(calls)):
            execute(self.root, plan, directory, native_only=True, phases=['trust'])
        self.assertFalse((directory / 'SelectedAudit.lean').exists())
        audit = (self.root / AUDIT_DRIVER).read_text()
        self.assertEqual(audit.count('import AglibTest.AuditSupport'), 1)
        audit_call = next(command for command in calls if AUDIT_DRIVER in command)
        self.assertEqual(json.loads(audit_call[-1]), [['AglibTest', 'AuditSupport']])
        self.assertIn('AglibAudit.auditModules selected', audit)
        self.assertIn('coverage.contains `AuditForeign.GeneratedDatum.rec', audit)
        self.assertIn('unless hidden.size == 1', audit)
        self.assertIn('(env.checked.get.find? hidden[0]!).isSome', audit)
        self.assertFalse(any('scripts/check_kernel.py' in ' '.join(c) for c in calls))
        self.assertTrue(any('scripts/check_compiled_inventory.py' in ' '.join(c) for c in calls))

    def test_changed_proof_reuses_controls_but_keeps_selected_trust_coverage(self):
        plan, calls = self.changed_plan(), []
        self.assertTrue(plan['trust'])
        self.assertFalse(plan['controls'])
        with patch('check_affected.run', side_effect=self.native_mock(calls)):
            execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True, phases=['trust'])
        text = [' '.join(command) for command in calls]
        self.assertTrue(any('/SelectedAudit.lean' in command for command in text))
        self.assertTrue(any('check_compiled_inventory.py --modules Aglib.Base' in command for command in text))
        self.assertFalse(any('check_kernel.py' in command for command in text))
        self.assertFalse(any('check_negative_controls.py' in command for command in text))

    def test_ordinary_local_final_checks_keep_trust_and_export_without_replay_claims(self):
        plan, calls = self.changed_plan(), []
        directory = Path(self.temp.name) / 'run'
        output = directory / 'outputs.jsonl'
        with patch('check_affected.run', side_effect=self.native_mock(calls)):
            execute(self.root, plan, directory, native_only=True, outputs=output)
        text = [' '.join(command) for command in calls]
        self.assertFalse(any('check_kernel.py' in command for command in text))
        self.assertTrue(any('SelectedAudit.lean' in command for command in text))
        self.assertTrue(any('check_compiled_inventory.py' in command for command in text))
        self.assertTrue(any('Audit.lean' in command and 'client-audit' in command for command in text))
        coverage = json.loads(output.with_suffix('.jsonl.coverage.json').read_text())
        self.assertEqual(coverage['kernel_replay'],
                         'not-requested; formal-acceptance evidence tracked externally')
        self.assertEqual(coverage['negative_controls'],
                         'unchanged-inputs; prior-compatible-coverage-required')
        self.assertNotIn('independent_replay', coverage)

    def test_auditor_controls_and_runtime_changes_trigger_rejection_controls(self):
        inputs = ['AglibTest/AuditSupport.lean', 'AglibTest/Axioms.lean',
                  'AglibTest/AuditCoverage.lean', 'AglibTest/NegativeControls/ImportedFixture.lean',
                  'scripts/check_negative_controls.py', 'scripts/resource_guard.py', 'scripts/build_serial.py']
        for path in inputs:
            with self.subTest(path=path):
                target = self.root / path
                previous = target.read_text() if target.exists() else None
                self.write(path, (previous or '') + '\n-- changed control input\n')
                plan = select(self.root, self.base)
                self.assertTrue(plan['controls'])
                self.assertTrue(plan['trust'])
                self.assertTrue(plan['native'])
                if previous is None:
                    target.unlink()
                else:
                    target.write_text(previous)
        self.write('scripts/check_negative_controls.py', '# changed checker\n')
        plan, calls = select(self.root, self.base), []
        with patch('check_affected.run', side_effect=self.native_mock(calls)):
            execute(self.root, plan, Path(self.temp.name) / 'run', native_only=True, ci=True, phases=['trust'])
        self.assertTrue(any('scripts/check_negative_controls.py' in command for command in calls))

    def test_workflow_gates_native_setup_and_never_rebuilds_for_export(self):
        workflow = (Path(__file__).resolve().parents[1] / '.github/workflows/ci.yml').read_text()
        scope = workflow.index('id: scope')
        install = workflow.index('- name: Install the pinned Lean toolchain')
        self.assertLess(scope, install)
        for name in ['Install the pinned Lean toolchain', 'Restore third-party proof cache',
                     'Fetch matching Mathlib proof cache', 'Restore shared native Lake artifacts',
                     'Restore incremental project builds', 'Run CI checks for the library and independent client',
                     'Publish native artifacts for downstream dependencies']:
            step = workflow.split('- name: ' + name, 1)[1].split('      - name:', 1)[0]
            self.assertIn("steps.scope.outputs.native == 'true'", step)
        self.assertNotIn('scripts/build_serial.py', workflow)
        self.assertNotIn('Aglib AglibTest', workflow)
        self.assertIn('native-outputs.jsonl.coverage.json', workflow)
        self.assertIn('validation-coverage.json', workflow)
        commands = [workflow.index('python3 scripts/ci_pipeline.py ' + phase)
                    for phase in ('plan', 'source', 'native', 'finalize')]
        self.assertEqual(commands, sorted(commands))
        self.assertLess(commands[1], install)
        self.assertIn('--head "$GITHUB_SHA"', workflow)
        self.assertIn('--requested-base "$REQUESTED_BASE"', workflow)
        self.assertIn('Optional older comparison commit', workflow)
        self.assertNotIn('github.event.before', workflow)
        finalizer = workflow.split('- name: Finalize complete CI coverage', 1)[1].split('      - name:', 1)[0]
        self.assertIn("always() && steps.scope.outcome == 'success'", finalizer)
        self.assertNotIn('steps.scope.outputs.native', finalizer)
        self.assertIn('--outputs "$RUNNER_TEMP/native-outputs.jsonl"', finalizer)
        publication = workflow.split('- name: Publish native artifacts for downstream dependencies', 1)[1].split('      - name:', 1)[0]
        self.assertIn("steps.finalize.outcome == 'success'", publication)
        self.assertIn("steps.scope.outputs.publish == 'true'", publication)
        self.assertIn("github.event_name == 'push'", publication)
        self.assertIn("github.ref == 'refs/heads/main'", publication)


if __name__ == '__main__':
    unittest.main()
