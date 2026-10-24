"""Compatible native-command retry tests using explicit synthetic execution."""
import unittest

from test_shared import CHECK, NativeFixture


class RetryTests(NativeFixture):
    def test_failure_retries_failed_work_and_reuses_earlier_compatible_successes(self):
        self.runtime.fail = lambda command: command[:3] == ['lake', '--no-build', 'lint']
        with self.assertRaisesRegex(ValueError, 'Native checks failed: lint'):
            self.check()
        self.runtime.fail = None
        self.runtime.calls.clear()
        result = self.check()
        self.assertEqual(result['reused_checks'], ['source-0', 'entries-Quartz', 'text-style', 'axioms-Quartz'])
        self.assertEqual(result['performed_checks'], ['lint'])
        self.assertNotIn(list(CHECK), self.runtime.calls)
        self.assertIn(['lake', 'test'], self.runtime.calls)

    def test_native_hardlink_activity_during_lint_reaches_audit_and_reuses_results(self):
        artifact = self.root / '.lake/build/lib/lean/Quartz/Base.olean'
        def link_while_lint_runs(command):
            if command[:3] == ['lake', '--no-build', 'lint']:
                link = self.scratch / 'peer-workspace.olean'
                import os
                os.link(artifact, link)
                link.unlink()
        self.runtime.callback = link_while_lint_runs
        first = self.check()
        self.assertIn('axioms-Quartz', first['performed_checks'])
        self.runtime.callback = None
        self.runtime.calls.clear()
        second = self.check()
        self.assertIn('lint', second['reused_checks'])
        self.assertIn('axioms-Quartz', second['reused_checks'])
        self.assertNotIn(['lake', '--no-build', 'lint', 'Quartz', '--', '--trace'], self.runtime.calls)

    def test_checker_preparation_and_test_failures_do_not_suppress_axiom_feedback(self):
        for target in ('tools', 'test'):
            with self.subTest(target=target):
                self.runtime.fail = lambda command: (command[:3] == ['lake', '--rehash', 'build']
                    and 'batteries/runLinter' in command if target == 'tools' else command == ['lake', 'test'])
                with self.assertRaisesRegex(ValueError, 'Native checks failed: ' + target):
                    self.check()
                result = next(row for row in self.summaries() if target in row.get('failed_checks', {}))
                self.assertIn('axioms-Quartz', result['performed_checks'] + result['reused_checks'])
                self.runtime.calls.clear()
        self.runtime.fail = None

    def test_fatal_runtime_or_cancellation_never_launches_later_audit(self):
        from lean_ci.runtime import RuntimeFailure
        for reason in ('KeyboardInterrupt', 'owned process group unresolved'):
            with self.subTest(reason=reason):
                def fail_at_lint(command):
                    if command[:3] == ['lake', '--no-build', 'lint']:
                        raise RuntimeFailure(reason)
                self.runtime.callback = fail_at_lint
                with self.assertRaisesRegex(RuntimeFailure, reason):
                    self.check()
                self.assertNotIn(['lake', 'env', str(self.auditor), '--root', 'Quartz'], self.runtime.calls)
                self.runtime.calls.clear()
        self.runtime.callback = None

    def test_additional_source_policy_scope_is_guarded_through_export(self):
        from lean_ci.local import SourceCheck
        from lean_ci.state import InputDrift
        client = self.root / 'examples/downstream'
        client.mkdir(parents=True)
        check = SourceCheck(CHECK, source_roots=(client,))
        def add_source(command):
            if command[:3] == ['lake', '--no-build', 'lint']:
                (client / 'New.lean').write_text('module\n')
        self.runtime.callback = add_source
        with self.assertRaises((InputDrift, ValueError)):
            self.check(source_checks=(check,), outputs=self.outputs)
        self.assertFalse(self.outputs.exists())

    def test_extra_source_added_after_policy_selection_is_in_initial_binding(self):
        from lean_ci.local import SourceCheck
        client = self.root / 'examples/downstream'
        check = SourceCheck(CHECK, source_roots=(client,))
        client.mkdir(parents=True)
        (client / 'BeforeStart.lean').write_text('module\n')
        self.check(source_checks=(check,))
        source = next(row for row in self.records() if row['binding']['kind'] == 'source-0')
        self.assertIn('examples/downstream/BeforeStart.lean', source['binding']['raw_inputs'])

    def test_unchanged_checks_reuse_exact_compatible_records(self):
        first = self.check()
        second = self.check()
        self.assertEqual(second['reused_checks'], first['performed_checks'])
        self.assertEqual(second['performed_checks'], [])
        self.assertTrue(all(record['status'] == 'success' for record in self.records()))
        self.assertTrue(all(record['binding']['arguments'] == record['executed_command']
                            for record in self.records()))
        lint = next(record for record in self.records() if record['binding']['kind'] == 'lint')
        self.assertIsNotNone(lint['binding']['reflective_imports'])
        self.assertEqual(lint['receipt']['exit_code'], 0)
        self.assertTrue(lint['receipt']['owned_group_gone'])

    def test_unrelated_nonproduction_source_preserves_production_check_successes(self):
        unrelated = self.root / 'Unrelated.lean'
        unrelated.write_text('module\ndef unrelated := 1\n')
        self.check()
        unrelated.write_text('module\ndef unrelated := 2\n')
        result = self.check()
        required = {'entries-Quartz', 'text-style', 'lint', 'axioms-Quartz'}
        self.assertTrue(required.issubset(result['reused_checks']))
        self.assertTrue(required.isdisjoint(result['performed_checks']))

    def test_reused_checker_native_observations_remain_guarded_until_export(self):
        self.check()
        artifact = self.root / '.lake/build/lib/lean/Batteries/Tactic/Lint.olean'
        audit = ['lake', 'env', str(self.auditor), '--root', 'Quartz']
        # Force this final command to execute after an earlier reused lint result.
        self.auditor.write_bytes(b'updated prepared auditor')
        self.runtime.calls.clear()

        def mutate_later(command):
            if command == audit:
                artifact.write_bytes(b'mutated after earlier lint success was reused')

        self.runtime.callback = mutate_later
        with self.assertRaises(ValueError):
            self.check(outputs=self.outputs)
        self.assertNotIn(['lake', '--no-build', 'lint', 'Quartz', '--', '--trace'],
                         self.runtime.calls)
        self.assertEqual(self.runtime.calls.count(audit), 1)
        self.assertFalse(self.outputs.exists())
        self.assertIn('failed', [summary['status'] for summary in self.summaries()])

    def test_changed_source_invalidates_its_raw_and_reflective_checks(self):
        self.check()
        (self.root / 'Quartz/Base.lean').write_text('module\ndef changed := 2\n')
        result = self.check()
        self.assertEqual(result['reused_checks'], ['entries-Quartz'])
        self.assertEqual(result['performed_checks'], ['source-0', 'text-style',
                                                     'lint', 'axioms-Quartz'])

    def test_production_source_addition_and_removal_invalidate_entry_enrollment(self):
        existing = self.root / 'Quartz/Existing.lean'
        existing.write_text('module\ndef existing := 1\n')
        self.check()
        added = self.root / 'Quartz/Added.lean'
        added.write_text('module\ndef added := 1\n')
        addition = self.check()
        self.assertIn('entries-Quartz', addition['performed_checks'])
        self.assertIn('lint', addition['reused_checks'])
        self.assertIn('axioms-Quartz', addition['reused_checks'])
        existing.unlink()
        removal = self.check()
        self.assertIn('entries-Quartz', removal['performed_checks'])
        self.assertIn('lint', removal['reused_checks'])
        self.assertIn('axioms-Quartz', removal['reused_checks'])

    def test_changed_compiled_import_invalidates_native_checks_only(self):
        self.check()
        (self.root / '.lake/build/lib/lean/Quartz/Base.olean').write_bytes(b'changed native bytes')
        result = self.check()
        self.assertIn('source-0', result['reused_checks'])
        self.assertIn('lint', result['performed_checks'])
        self.assertIn('axioms-Quartz', result['performed_checks'])

    def test_changed_source_checker_invalidates_only_that_source_check(self):
        self.check()
        (self.root / 'scripts/check_sources.py').write_text('# different checker\n')
        result = self.check()
        self.assertIn('source-0', result['performed_checks'])
        self.assertIn('lint', result['reused_checks'])
        self.assertIn('axioms-Quartz', result['reused_checks'])

    def test_shared_source_parser_change_invalidates_source_guards_only(self):
        parser = self.root / 'scripts/lean_ci/source.py'
        parser.parent.mkdir()
        parser.write_text('# original source grammar\n')
        self.check()
        parser.write_text('# changed source grammar\n')
        result = self.check()
        self.assertEqual(result['performed_checks'], ['source-0'])
        self.assertEqual(result['reused_checks'], ['entries-Quartz', 'text-style',
                                                   'lint', 'axioms-Quartz'])

    def test_changed_mathlib_helper_source_invalidates_its_success(self):
        self.check()
        source = self.helper_sources['mk_all']
        source.write_text(source.read_text() + '-- changed checker implementation\n')
        result = self.check()
        self.assertEqual(result['performed_checks'], ['entries-Quartz'])
        self.assertIn('text-style', result['reused_checks'])
        self.assertIn('lint', result['reused_checks'])

    def test_changed_mathlib_helper_binary_invalidates_its_success(self):
        self.check()
        self.helper_binaries['lint-style'].write_bytes(b'changed style executable')
        result = self.check()
        self.assertEqual(result['performed_checks'], ['text-style'])
        self.assertIn('entries-Quartz', result['reused_checks'])
        self.assertIn('lint', result['reused_checks'])

    def test_changed_checker_native_import_invalidates_only_its_consumer(self):
        self.check()
        artifact = self.mathlib / '.lake/build/lib/lean/Mathlib/TextChecks.olean'
        artifact.write_bytes(b'changed compiled checker dependency')
        result = self.check()
        self.assertEqual(result['performed_checks'], ['text-style'])
        self.assertIn('entries-Quartz', result['reused_checks'])
        self.assertIn('axioms-Quartz', result['reused_checks'])

    def test_changed_auditor_binary_invalidates_its_success(self):
        self.check()
        self.auditor.write_bytes(b'different upstream auditor executable')
        result = self.check()
        self.assertEqual(result['performed_checks'], ['axioms-Quartz'])
        self.assertIn('lint', result['reused_checks'])

    def test_changed_options_and_compiler_identity_invalidate_native_success(self):
        self.check()
        self.runtime.environment['LEAN_OPTIONS'] = '-DmaxRecDepth=2000'
        options = self.check()
        self.assertIn('lint', options['performed_checks'])
        self.assertIn('axioms-Quartz', options['performed_checks'])
        self.runtime.toolchain['lean'] = 'different-compiler'
        compiler = self.check()
        self.assertIn('lint', compiler['performed_checks'])
        self.assertIn('axioms-Quartz', compiler['performed_checks'])

    def test_missing_native_metadata_disables_reuse_without_waiving_checks(self):
        self.check()
        (self.root / '.lake/build/lib/lean/Quartz/Base.ilean').unlink()
        for attempt in range(2):
            with self.subTest(attempt=attempt):
                result = self.check()
                self.assertIn('lint', result['performed_checks'])
                self.assertIn('axioms-Quartz', result['performed_checks'])
                self.assertNotIn('lint', result['reused_checks'])


if __name__ == '__main__':
    unittest.main()
