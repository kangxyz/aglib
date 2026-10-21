"""Configured Application uses the common runner, recipes and narrow bindings."""
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from lean_ci.configured import create_application
from lean_ci.application import Application
from lean_ci.project.scope import select_scope
from tests.project.test_configuration import Fixture


class ConfiguredTests(Fixture):
    def test_factory_explicit_package_coordinate(self):
        application = create_application(self.root)
        self.assertIsInstance(application, Application)
        self.assertEqual(application.package_cwd, self.root.resolve())

    def test_recipe_orders_groups_and_canonical_origin_batch(self):
        self.commit()
        self.write('Tiny/Base.lean', 'module\ndef base := 2\n')
        application = create_application(self.root)
        plan = application.adapter.select_scope(self.root, source_basis={'kind': 'working-tree'})
        tasks = application._tasks(plan, 'check', self.root.parent / 'external-configured-run')
        builds = [t for t in tasks if t['kind'] == 'build']
        self.assertEqual([t['modules'] for t in builds], [['Tiny.Base'], ['Tiny', 'Tiny.Consumer'], ['TinyTest.Positive']])
        self.assertTrue(all(t['command'][:3] == ['lake', '--rehash', 'build'] for t in builds))
        declaration = [t for t in tasks if t.get('check_kind') == 'declarations']
        self.assertTrue(all(t['check_batch']['mode'] == 'canonical-prefix' for t in declaration))
        self.assertTrue(all(len(t['modules']) == 1 for t in declaration))
        self.assertLess(tasks.index(next(t for t in tasks if t['id'] == 'root/declarations/Tiny.Base')), tasks.index(builds[1]))

    def test_source_only_does_not_discover_native_environment(self):
        self.commit()
        self.write('README.md', 'docs\n')
        application = create_application(self.root)
        plan = application.adapter.select_scope(self.root, source_basis={'kind': 'working-tree'})
        tasks = application._tasks(plan, 'check', self.root.parent / 'external-configured-run')
        self.assertEqual([t['check_kind'] for t in tasks], ['source'])
        self.assertFalse(tasks[0]['native'])

    def test_history_initial_is_not_fake_verified_base(self):
        self.commit()
        application = create_application(self.root)
        history = SimpleNamespace(select_baseline=lambda *a, **k: {'kind': 'initial'})
        with patch.dict('sys.modules', {'lean_ci.transport.history': history}):
            plan = application.adapter.plan(self.root, 'example/tiny', 'main', self.git('rev-parse', 'HEAD'))
        self.assertTrue(plan['scope']['initial'])
        self.assertIsNone(plan['scope']['base'])

    def test_history_api_error_is_not_bootstrap(self):
        self.commit()
        application = create_application(self.root)
        def unavailable(*args, **kwargs):
            raise RuntimeError('network unavailable')
        with patch.dict('sys.modules', {'lean_ci.transport.history': SimpleNamespace(select_baseline=unavailable)}):
            with self.assertRaisesRegex(RuntimeError, 'network'):
                application.adapter.plan(self.root, 'example/tiny', 'main', self.git('rev-parse', 'HEAD'))

    def test_style_binding_has_no_subject_olean(self):
        self.commit()
        self.write('Tiny/Base.lean', 'def base := 2\n')
        application = create_application(self.root)
        config = application.adapter.config(self.root)
        task = application.adapter._check(self.root, config, 'style', origins=['Tiny.Base'], paths=['Tiny/Base.lean'])
        checker = SimpleNamespace(checker_inputs=lambda *a, **k: (), runtime_roots=lambda k: ())
        with patch.dict('sys.modules', {'lean_ci.checks.native': checker}):
            binding = application.adapter.binding(self.root, task, {})
        self.assertEqual(binding['native'], {})
        self.assertIn(str(self.root / 'Tiny/Base.lean'), binding['raw_inputs'])
        self.assertNotIn(str(self.root / '.github/lean-ci.toml'), binding['raw_inputs'])

    def test_formal_and_negative_fixtures_never_positive_build_targets(self):
        self.write('TinyTest/Negative.lean', '#check missing\n')
        self.write('TinyTest/Formal.lean', 'axiom formal : True\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('[roles]', 'expected_failure=["TinyTest/Negative.lean"]\nformal_only=["TinyTest/Formal.lean"]\n[roles]'))
        self.commit()
        application = create_application(self.root)
        scope = select_scope(self.root, initial=True)
        tasks = application._tasks({'scope': scope}, 'native', self.root.parent / 'external-configured-run')
        built = {n for t in tasks if t['kind'] == 'build' for n in t['modules']}
        self.assertNotIn('TinyTest.Negative', built)
        self.assertNotIn('TinyTest.Formal', built)
        self.assertTrue(any(t.get('check_kind') == 'expected-failure' for t in tasks))

    def test_native_checker_binding_ignores_unrelated_config_bytes(self):
        self.commit()
        application = create_application(self.root)
        config = application.adapter.config(self.root)
        task = application.adapter._check(self.root, config, 'declarations', origins=['Tiny.Base'])
        checker = SimpleNamespace(checker_inputs=lambda *a, **k: (), runtime_roots=lambda k: ())
        with patch.dict('sys.modules', {'lean_ci.checks.native': checker}), patch('lean_ci.execution.state.module_identity', return_value={'fixture': 'native-identity'}):
            before = application.adapter.binding(self.root, task, {})
            path = self.root / '.github/lean-ci.toml'
            path.write_text('# reporting-only comment\n' + path.read_text())
            after = application.adapter.binding(self.root, task, {})
        self.assertEqual(before, after)

    def test_control_suite_is_one_task_for_multiple_control_sources(self):
        self.write('TinyTest/ControlA.lean', 'def ca := 1\n')
        self.write('TinyTest/ControlB.lean', 'def cb := 2\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('[roles]', 'controls=["TinyTest/ControlA.lean","TinyTest/ControlB.lean"]\n[roles]'))
        self.commit()
        application = create_application(self.root)
        tasks = application._tasks({'scope': select_scope(self.root, initial=True)}, 'native', self.root.parent / 'external-configured-run')
        controls = [t for t in tasks if t.get('check_kind') == 'controls']
        self.assertEqual(len(controls), 1)
        self.assertEqual(len(controls[0]['raw_paths']), 2)

    def test_style_and_builtin_runtime_are_shared_by_coherent_groups(self):
        self.commit()
        self.write('Tiny/Base.lean', 'def base := 2\n')
        self.write('Tiny/Consumer.lean', 'import Tiny.Base\ndef consumer := base\n-- edit\n')
        application = create_application(self.root)
        plan = application.adapter.select_scope(self.root, source_basis={'kind': 'working-tree'})
        tasks = application._tasks(plan, 'check', self.root.parent / 'external-configured-run')
        styles = [t for t in tasks if t.get('check_kind') == 'style']
        self.assertEqual(len(styles), 1)
        self.assertEqual(styles[0]['origins'], ['Tiny.Base', 'Tiny.Consumer'])
        builtins = [t for t in tasks if t.get('check_kind') == 'builtin']
        self.assertEqual(len(builtins), 3)
        self.assertEqual(builtins[0]['command'], ['lake', '--no-build', 'lint', '--builtin-only', 'Tiny.Base', 'Tiny.Consumer'])
        self.assertTrue(all(t['check_batch']['mode'] == 'canonical-prefix' for t in tasks if t.get('check_kind') in {'declarations', 'axioms', 'inventory'}))
        axioms = [t for t in tasks if t.get('check_kind') == 'axioms']
        self.assertTrue(all(t['covers'] == ['axioms', 'inventory'] for t in axioms))
        self.assertFalse(any(t.get('check_kind') == 'inventory' for t in tasks))

    def test_changed_markdown_is_explicit_source_input(self):
        self.commit()
        self.write('docs/Guide.md', 'Updated documentation\n')
        application = create_application(self.root)
        plan = application.adapter.select_scope(self.root, source_basis={'kind': 'working-tree'})
        source = application._tasks(plan, 'check', self.root.parent / 'external-configured-run')[0]
        self.assertEqual(source['command'][-2:], ['--changed-path', 'docs/Guide.md'])
        self.assertIn('docs/Guide.md', source['raw_paths'])
        self.assertIn('docs/Guide.md', application.adapter.local_inputs(self.root))

    def test_markdown_binding_tracks_target_namespace_without_reading_payload(self):
        self.commit()
        self.write('docs/Guide.md', '[Details](../data/item.bin)\n')
        self.write('data/item.bin', 'large payload v1\n')
        application = create_application(self.root)
        plan = application.adapter.select_scope(self.root, source_basis={'kind': 'working-tree'})
        task = application._tasks(plan, 'check', self.root.parent / 'external-configured-run')[0]
        checker = SimpleNamespace(checker_inputs=lambda *a, **k: (), runtime_roots=lambda k: ())
        with patch.dict('sys.modules', {'lean_ci.checks.native': checker}):
            before = application.adapter.binding(self.root, task, {})
            self.write('data/item.bin', 'different payload bytes\n')
            changed_payload = application.adapter.binding(self.root, task, {})
            (self.root / 'data/item.bin').unlink()
            missing = application.adapter.binding(self.root, task, {})
        self.assertEqual(before, changed_payload)
        self.assertNotEqual(before, missing)
        self.assertEqual(before['markdown_targets'], [{'path': 'docs/../data/item.bin', 'resolved': 'data/item.bin', 'kind': 'file'}])
        self.assertNotIn(str(self.root / 'data/item.bin'), before['raw_inputs'])


class ConfiguredSourcePolicyTests(Fixture):
    def test_exception_removal_reaches_extra_source_without_native_style(self):
        import json
        from lean_ci.checks.guards import check_source
        self.write('Tools/Fixture.lean', 'axiom fixture : True\n')
        policy = {'schema': 1, 'kind': 'source_exceptions',
                  'token_exceptions': {'Tools/Fixture.lean': {'axiom': 'Intentional source-policy fixture.'}}}
        self.write('policy/exceptions.json', json.dumps(policy))
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text() + '[sources]\nsupport=["Tools"]\n[policy]\nexceptions=["policy/exceptions.json"]\n')
        self.commit()
        self.assertEqual(check_source(self.root, create_application(self.root).adapter.config(self.root), ['Tools/Fixture.lean']), [])
        policy['token_exceptions'] = {}
        self.write('policy/exceptions.json', json.dumps(policy))
        app = create_application(self.root)
        plan = app.adapter.select_scope(self.root, source_basis={'kind': 'working-tree'})
        tasks = app._tasks(plan, 'check', self.root.parent / 'source-policy-run')
        self.assertEqual(len(tasks), 1)
        self.assertEqual(tasks[0]['check_kind'], 'source')
        selected = json.loads(tasks[0]['generated'])
        self.assertIn('Tools/Fixture.lean', selected)
        self.assertEqual(plan['scope']['source_style'], [])
        self.assertEqual(plan['scope']['modules'], [])
        errors = check_source(self.root, app.adapter.config(self.root), selected)
        self.assertTrue(any('Tools/Fixture.lean:1: forbidden token axiom' in e for e in errors))


class ExtraSpecialEnrollmentTests(Fixture):
    def test_config_only_extra_expected_failure_runs_and_rejects_unexpected_pass(self):
        import contextlib
        import io
        import json
        from lean_ci.checks.guards import run_controls
        self.write('Tools/ShouldFail.lean', 'def valid := 1\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text() + '[sources]\nsupport=["Tools/ShouldFail.lean"]\n')
        self.commit()
        path.write_text(path.read_text().replace('[roles]', 'expected_failure=["Tools/ShouldFail.lean"]\n[roles]'))
        app = create_application(self.root)
        plan = app.adapter.select_scope(self.root, source_basis={'kind': 'working-tree'})
        self.assertEqual(plan['scope']['expected_failure'], ['Tools/ShouldFail.lean'])
        self.assertTrue(plan['scope']['native'])
        self.assertEqual(plan['scope']['modules'], [])
        tasks = app._tasks(plan, 'native', self.root.parent / 'extra-negative-run')
        negative = next(t for t in tasks if t.get('check_kind') == 'expected-failure')
        selected = json.loads(negative['generated'])
        self.assertEqual(selected, [str(app.root / 'Tools/ShouldFail.lean')])
        with patch('lean_ci.checks.native.lake_environment', return_value={'lean': 'fixture-lean'}), \
                patch('lean_ci.checks.guards.subprocess.run', return_value=SimpleNamespace(returncode=0, stdout='', stderr='')) as compiler, \
                contextlib.redirect_stdout(io.StringIO()):
            status = run_controls('expected-failure', Path(negative['cwd']), app.root,
                                  app.adapter.config(app.root), selected)
        self.assertEqual(status, 1)
        compiler.assert_called_once()
        self.assertEqual(compiler.call_args.args[0], ['fixture-lean', str(app.root / 'Tools/ShouldFail.lean')])

    def test_extra_compile_pass_control_rejected_before_planning(self):
        from lean_ci.project.configuration import load_config
        self.write('Tools/Control.lean', 'def valid := 1\n')
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('[roles]', 'controls=["Tools/Control.lean"]\n[roles]') + '[sources]\nsupport=["Tools/Control.lean"]\n')
        with self.assertRaisesRegex(ValueError, 'Compile-pass control requires an enrolled Lake module identity'):
            load_config(self.root)

    def test_config_only_module_control_is_retained(self):
        self.write('TinyTest/Control.lean', 'def valid := 1\n')
        self.commit()
        path = self.root / '.github/lean-ci.toml'
        path.write_text(path.read_text().replace('[roles]', 'controls=["TinyTest/Control.lean"]\n[roles]'))
        app = create_application(self.root)
        plan = app.adapter.select_scope(self.root, source_basis={'kind': 'working-tree'})
        self.assertEqual(plan['scope']['controls'], ['TinyTest/Control.lean'])
        self.assertTrue(plan['scope']['native'])
        tasks = app._tasks(plan, 'native', self.root.parent / 'module-control-run')
        self.assertTrue(any(t.get('check_kind') == 'controls' for t in tasks))
        self.assertNotIn('TinyTest.Control', plan['scope']['modules'])
