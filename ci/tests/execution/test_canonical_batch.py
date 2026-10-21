"""Fixed-driver synthetic resource/sidecar tests; no production Lean is run."""
from contextlib import nullcontext
from copy import deepcopy
import json
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from lean_ci.execution.batch import check_group, valid_batch_evidence
from lean_ci.execution.runner import EXECUTION_CACHE_OWNERS, TaskRunner
from lean_ci.execution.resources import ResourceConfig
from lean_ci.execution.runtime import NativeRuntime
from lean_ci.execution.state import (CheckInputs, InputDrift, Progress, ReflectionGraph,
    TemporalInputs, digest, read_json, valid_receipt, valid_success, write_json)

import tests.execution.test_engine as fixtures


class Policy:
    def binding(self, root, task, toolchain, reflection=None, observations=None):
        name = task['modules'][0]
        return {'arguments': task['command'],
                'source': observations.hash_file(root / (name + '.lean')),
                'reflective_imports': {'synthetic': name}}


class CanonicalBatchTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='canonical-batch-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        for name in ('A', 'B', 'C', *('N' + str(n) for n in range(17))):
            (self.root / (name + '.lean')).write_text('module\n')
        self.config = self.root / 'config.toml'
        self.config.write_text('schema=1\n')
        self.runner = TaskRunner()
        self.runner.root = self.runner.package_cwd = self.root
        self.runtime = NativeRuntime(self.root, environment={'PRESERVED': 'wrapper'})
        self.runner.runtime = self.runtime
        self.runner.adapter = Policy()
        self.plan = {'repository': 'synthetic-fixture', 'implementation': {'fixed': 'test-driver'}}
        self.progress = self.root / 'progress'
        self.calls, self.shared = [], []
        self.fail, self.missing, self.callback, self.forge = None, None, None, None
        self.code, self.guard, self.closed, self.fragment = 0, None, True, False
        self.addCleanup(patch.stopall)
        patch('lean_ci.execution.runtime.resources.limits', return_value={'fixture': True}).start()
        patch('lean_ci.execution.runtime.build.build_threads', return_value=2).start()
        patch('lean_ci.execution.runtime.build.capped_toolchain',
              return_value=nullcontext(dict(self.runtime.environment, LEAN='fixture-wrapper'))).start()
        patch('lean_ci.execution.runtime.resources.run', side_effect=self.execute).start()

    def task(self, name, kind='declarations'):
        return {'id': kind + '/' + name, 'kind': 'check', 'check_kind': kind,
                'cwd': str(self.root), 'modules': [name], 'capped': True,
                'command': [sys.executable, '-m', 'lean_ci.checks.native', kind,
                            '--root', str(self.root), '--config', str(self.config), '--modules', name],
                'check_batch': {'id': 'current-composition', 'mode': 'canonical-prefix',
                                'read_only': True, 'single_process': True}}

    def execute(self, command, **kwargs):
        self.assertEqual(kwargs['env']['PRESERVED'], 'wrapper')
        self.assertEqual(kwargs['env']['LEAN'], 'fixture-wrapper')
        self.assertEqual(kwargs['budget']['native_build_threads'], 2)
        self.assertIs(kwargs['config'], self.runtime.resource_config)
        selection = read_json(command[command.index('--selection-json') + 1])
        records = []
        self.calls.append([item['module'] for item in selection['items']])
        for item in selection['items']:
            if item['module'] == self.missing:
                continue
            record = {key: item[key] for key in ('id', 'module', 'input_key')}
            record.update(kind=selection['kind'], invocation=selection['invocation'],
                          completed=True, success=item['module'] != self.fail)
            records.append(record)
        if self.forge:
            self.forge(records)
        sidecar = Path(command[command.index('--results-jsonl') + 1])
        sidecar.write_text(''.join(json.dumps(row) + '\n' for row in records)
                           + ('{"incomplete":' if self.fragment else ''))
        if self.callback:
            self.callback()
        receipt = {'state': 'completed', 'command': command, 'cwd': str(kwargs['cwd']),
                   'exit_code': self.code, 'guard_failure': self.guard, 'owned_group_gone': self.closed}
        write_json(kwargs['receipt'], receipt)
        return self.code

    def run_group(self, names=('A', 'B'), observations=None):
        return self.runner.run_tasks(self.plan, [self.task(name) for name in names],
            self.root / 'run', self.progress, {}, observations or TemporalInputs())

    def successes(self):
        return [read_json(p) for p in self.progress.glob('*.json')]

    def test_real_runtime_path_shares_one_actual_command_and_verifies(self):
        actual = self.run_group()
        self.assertEqual(self.calls, [['A', 'B']])
        for item in actual:
            success = item['result']['success']
            self.assertEqual(success['evidence'], 'canonical-prefix-v1')
            self.assertIn('--selection-json', success['executed_command'])
            self.assertNotIn('--modules', success['executed_command'])
            self.assertEqual(success['receipt']['command'], success['executed_command'])
            self.assertTrue(valid_success(success, success['binding']))
        self.runner.verify_tasks(self.plan, [self.task('A'), self.task('B')], actual, {}, TemporalInputs())
        self.runner.assert_verified_inputs(self.runner._verified_inputs.whole)

    def test_audit_kinds_share_only_their_own_fixed_native_command(self):
        for kind in ('axioms', 'inventory'):
            with self.subTest(kind=kind):
                required = [self.task(name, kind) for name in ('A', 'B')]
                actual = self.runner.run_tasks(self.plan, required, self.root / kind,
                            self.progress, {}, TemporalInputs())
                self.assertEqual(self.calls[-1], ['A', 'B'])
                for item in actual:
                    success = item['result']['success']
                    self.assertEqual(success['batch']['selection']['kind'], kind)
                    self.assertEqual(success['batch']['command'][3], kind)
                    self.assertEqual(success['result']['kind'], kind)
                    self.assertTrue(valid_success(success, success['binding']))
                self.runner.verify_tasks(self.plan, required, actual, {}, TemporalInputs())
        # A different native predicate for the same origin cannot reuse a peer.
        self.assertEqual(len(self.calls), 2)
        self.assertEqual(len(self.successes()), 4)

    def test_cross_kind_commands_groups_selectors_and_rows_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'driver/configuration'):
            check_group([self.task('A'), self.task('B', 'axioms')], self.runtime)
        wrong_command = self.task('A', 'inventory')
        wrong_command['command'][3] = 'axioms'
        with self.assertRaisesRegex(ValueError, 'fixed exact-origin'):
            check_group([wrong_command], self.runtime)
        for kind in ('builtin', 'controls', 'arbitrary'):
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                check_group([self.task('A', kind)], self.runtime)
        actual = self.run_group()
        for change in ('selector', 'row'):
            forged = deepcopy(actual[0]['result']['success'])
            shared = forged['batch']
            if change == 'selector':
                shared['selection']['kind'] = 'axioms'
                shared['selection_sha256'] = digest(shared['selection'])
            else:
                shared['records'][0]['kind'] = 'inventory'
                shared['records_sha256'] = digest(shared['records'])
            with self.subTest(change=change):
                self.assertFalse(valid_success(forged, forged['binding']))
        self.forge = lambda rows: rows[0].update(kind='declarations')
        with self.assertRaisesRegex(ValueError, 'canonical batch evidence'):
            self.runner.run_tasks(self.plan, [self.task('C', 'axioms')], self.root / 'audit',
                                 self.progress, {}, TemporalInputs())

    def test_safe_python_path_flag_is_preserved_for_each_fixed_batch_kind(self):
        for kind in ('declarations', 'axioms', 'inventory'):
            with self.subTest(kind=kind):
                task = self.task('A', kind)
                task['command'].insert(1, '-P')
                actual = self.runner.run_tasks(self.plan, [task], self.root / kind,
                                self.progress, {}, TemporalInputs())
                success = actual[0]['result']['success']
                self.assertEqual(success['executed_command'][:5],
                                 [sys.executable, '-P', '-m', 'lean_ci.checks.native', kind])
                self.assertTrue(valid_success(success, success['binding']))
                self.runner.verify_tasks(self.plan, [task], actual, {}, TemporalInputs())
        for flag in ('-I', '-S', '-c'):
            task = self.task('A')
            task['command'].insert(1, flag)
            with self.subTest(flag=flag), self.assertRaises(ValueError):
                check_group([task], self.runtime)

    def test_finalization_reuses_content_only_with_fresh_native_guards(self):
        native = self.root / 'native.olean'
        native.write_bytes(b'fixture-native-artifact')
        real_binding = self.runner.adapter.binding
        self.runner.adapter.binding = lambda *args, **kwargs: dict(
            real_binding(*args, **kwargs), native=kwargs['observations'].native_hash_file(native))
        observations = TemporalInputs()
        actual = self.run_group(observations=observations)
        with patch('lean_ci.execution.state.file_hash', wraps=lambda p: __import__('hashlib').sha256(Path(p).read_bytes()).hexdigest()) as read:
            self.runner.verify_tasks(self.plan, [self.task('A'), self.task('B')],
                                     actual, {}, observations)
        self.assertNotIn(native, [Path(call.args[0]) for call in read.call_args_list])
        self.assertIn(native, self.runner._verified_inputs.native.files)
        link = self.root / 'link-native'
        os.link(native, link)
        link.unlink()
        with self.assertRaises(InputDrift):
            self.runner.assert_verified_inputs(observations)

    def test_changed_native_stamp_is_rehashed_and_changed_bytes_fail_finalization(self):
        native = self.root / 'native.olean'
        native.write_bytes(b'fixture-native-artifact')
        real_binding = self.runner.adapter.binding
        self.runner.adapter.binding = lambda *args, **kwargs: dict(
            real_binding(*args, **kwargs), native=kwargs['observations'].native_hash_file(native))
        observations = TemporalInputs()
        actual = self.run_group(observations=observations)
        # A fresh final consuming interval accepts harmless restored metadata
        # after actually rehashing; it never carries the old interval's graph.
        link = self.root / 'link-native'
        os.link(native, link)
        link.unlink()
        with patch('lean_ci.execution.state.file_hash', wraps=lambda p: __import__('hashlib').sha256(Path(p).read_bytes()).hexdigest()) as read:
            self.runner.verify_tasks(self.plan, [self.task('A'), self.task('B')],
                                     actual, {}, observations)
        self.assertIn(native, [Path(call.args[0]) for call in read.call_args_list])
        native.write_bytes(b'changed-native-artifact')
        with self.assertRaisesRegex(ValueError, 'stale/corrupt'):
            self.runner.verify_tasks(self.plan, [self.task('A'), self.task('B')],
                                     actual, {}, observations)

    def test_warm_origin_reuse_survives_different_batch_composition(self):
        self.run_group()
        actual = self.run_group(('A', 'C'))
        self.assertEqual(self.calls, [['A', 'B'], ['C']])
        self.assertEqual([item['result']['mode'] for item in actual], ['reused', 'performed'])
        self.runner.verify_tasks(self.plan, [self.task('A'), self.task('C')], actual, {}, TemporalInputs())

    def test_nonzero_group_retains_completed_success_without_fake_exit_zero(self):
        self.fail, self.code = 'B', 1
        with self.assertRaisesRegex(ValueError, 'failed/incomplete'):
            self.run_group()
        saved = self.successes()
        self.assertEqual([r['item']['module'] for r in saved], ['A'])
        self.assertEqual(saved[0]['receipt']['exit_code'], 1)
        self.assertFalse(valid_receipt(saved[0]['receipt']))
        self.assertTrue(valid_success(saved[0], saved[0]['binding']))
        self.fail, self.code = None, 0
        self.run_group()
        self.assertEqual(self.calls, [['A', 'B'], ['B']])

    def test_closed_interruption_retains_only_flushed_terminal_origins(self):
        self.missing, self.code, self.guard, self.fragment = 'B', -15, 'watchdog failed closed: interruption', True
        with self.assertRaisesRegex(ValueError, 'failed/incomplete'):
            self.run_group()
        self.assertEqual([r['item']['module'] for r in self.successes()], ['A'])

    def test_unclosed_group_cannot_save_any_peer(self):
        self.closed = False
        with self.assertRaisesRegex(ValueError, 'closed canonical'):
            self.run_group()
        self.assertEqual(self.successes(), [])

    def test_source_restore_drift_prevents_all_new_success(self):
        source = self.root / 'A.lean'
        def mutate():
            before = source.read_text()
            source.write_text(before + ' ')
            source.write_text(before)
        self.callback = mutate
        with self.assertRaises(InputDrift):
            self.run_group()
        self.assertEqual(self.successes(), [])

    def test_forged_identity_duplicate_and_incomplete_success_are_rejected(self):
        for forge in (lambda rows: rows[0].update(input_key='0' * 64),
                      lambda rows: rows[0].update(invocation='foreign'),
                      lambda rows: rows[0].update(module='C'),
                      lambda rows: rows[0].update(kind='axioms'),
                      lambda rows: rows[0].update(completed=False),
                      lambda rows: rows.append(dict(rows[0]))):
            with self.subTest(forge=forge):
                self.forge = forge
                with self.assertRaisesRegex(ValueError, 'canonical batch evidence'):
                    self.run_group()
                self.assertEqual(self.successes(), [])

    def test_final_verification_rejects_projection_and_shared_invocation_tampering(self):
        actual = self.run_group()
        def wrong_row(r):
            r['result']['input_key'] = '0' * 64
        def wrong_selection(r):
            r['batch']['selection']['items'][0]['input_key'] = '0' * 64
            r['batch']['selection_sha256'] = digest(r['batch']['selection'])
        def wrong_driver(r):
            r['batch']['command'][2] = 'arbitrary.command'
        for forge in (wrong_row, wrong_selection, wrong_driver,
                      lambda r: r['item'].update(id='declarations/B')):
            forged = deepcopy(actual)
            forge(forged[0]['result']['success'])
            with self.subTest(forge=forge), self.assertRaises(ValueError):
                self.runner.verify_tasks(self.plan, [self.task('A'), self.task('B')], forged, {}, TemporalInputs())

    def test_final_verification_rejects_conflicting_records_for_one_invocation(self):
        actual = self.run_group()
        forged = deepcopy(actual)
        forged[0] = deepcopy(forged[0])
        shared = forged[0]['result']['success']['batch']
        # This change keeps each item independently structurally valid but gives
        # one actual invocation two inconsistent terminal resource receipts.
        shared['receipt']['duration_seconds'] = 123
        with self.assertRaisesRegex(ValueError, 'Conflicting evidence'):
            self.runner.verify_tasks(self.plan, [self.task('A'), self.task('B')], forged, {}, TemporalInputs())

    def test_native_metadata_restore_drift_cannot_save_batch_peers(self):
        (self.root / 'Init.lean').write_text('module\n')
        for name in ('Init', 'A', 'B'):
            fixtures.native_fixture(self.root, name)
        search_output = self.root / 'search.txt'
        search_path = str(self.root / '.lake/build/lib/lean')
        search_output.write_text(search_path)
        environment = {'id': 'search', 'kind': 'environment', 'command': ['fixture-search'],
                       'cwd': str(self.root), 'environment_output': str(search_output)}

        class NativePolicy(Policy):
            def binding(self, root, task, toolchain, reflection=None, observations=None):
                value = super().binding(root, task, toolchain, reflection, observations)
                value['reflective_imports'] = reflection.closure(task['modules'])
                return value

        self.runner.adapter = NativePolicy()
        def mutate():
            metadata = self.root / '.lake/build/lib/lean/A.ilean'
            link = self.root / 'transient-link'
            os.link(metadata, link)
            link.unlink()
        self.callback = mutate
        result = {'receipt': dict(state='completed', command=environment['command'],
                  cwd=str(self.root), exit_code=0, guard_failure=None, owned_group_gone=True),
                  'search_path': [search_path], 'output_sha256': TemporalInputs().hash_file(search_output)}
        with patch.object(self.runtime, 'run', return_value=result):
            with self.assertRaises(InputDrift):
                self.runner.run_tasks(self.plan, [environment, self.task('A'), self.task('B')],
                    self.root / 'run', self.progress, {'installation': str(self.root / 'compiler')},
                    TemporalInputs())
        self.assertEqual(self.successes(), [])

    def implementation_plan(self):
        from lean_ci.application import implementation_sources
        return dict(self.plan, implementation={name: 'fixture:' + name
                    for name in implementation_sources()})

    def binding_for_plan(self, plan):
        return self.runner._binding(plan, self.task('A'), {}, None, TemporalInputs())

    def test_configured_cache_key_ignores_reporting_changes_but_binds_mechanics(self):
        self.runner.adapter.cache_implementation_owners = tuple(sorted(EXECUTION_CACHE_OWNERS))
        plan = self.implementation_plan()
        initial = self.binding_for_plan(plan)
        changed = deepcopy(plan)
        changed['implementation']['cli.py'] = 'changed-cli'
        changed['implementation']['transport/history.py'] = 'changed-history'
        self.assertEqual(self.binding_for_plan(changed), initial)
        for owner in EXECUTION_CACHE_OWNERS:
            changed = deepcopy(plan)
            changed['implementation'][owner] = 'changed-mechanic'
            with self.subTest(owner=owner):
                self.assertNotEqual(self.binding_for_plan(changed), initial)
        # Neither binding nor the narrowed cache identity mutates the full plan.
        self.assertIn('cli.py', plan['implementation'])
        self.assertEqual(initial['execution']['implementation'],
            {owner: plan['implementation'][owner] for owner in EXECUTION_CACHE_OWNERS})

    def test_legacy_cache_key_retains_full_implementation_identity(self):
        plan = self.implementation_plan()
        initial = self.binding_for_plan(plan)
        changed = deepcopy(plan)
        changed['implementation']['cli.py'] = 'changed-cli'
        self.assertNotEqual(self.binding_for_plan(changed), initial)
        self.assertEqual(initial['execution']['implementation'], plan['implementation'])

    def test_cache_implementation_owners_reject_missing_mutable_and_unknown_names(self):
        owners = tuple(sorted(EXECUTION_CACHE_OWNERS))
        for invalid in (None, (), list(owners), owners[:-1], (*owners, owners[0]),
                        (*owners, 'not-an-implementation-owner.py'), (*owners, 7)):
            with self.subTest(owners=invalid):
                self.runner.adapter.cache_implementation_owners = invalid
                with self.assertRaisesRegex(ValueError, 'actual planned execution mechanics'):
                    self.binding_for_plan(self.implementation_plan())
        self.runner.adapter.cache_implementation_owners = owners
        plan = self.implementation_plan()
        del plan['implementation'][owners[0]]
        with self.assertRaisesRegex(ValueError, 'actual planned execution mechanics'):
            self.binding_for_plan(plan)

    def test_ordinary_progress_keeps_strict_exit_zero_policy(self):
        binding = {'arguments': ['ordinary-check']}
        receipt = {'state': 'completed', 'command': ['ordinary-check'], 'cwd': str(self.root),
                   'exit_code': 1, 'guard_failure': None, 'owned_group_gone': True}
        progress = Progress(self.progress)
        with self.assertRaises(ValueError):
            progress.save(binding, receipt, receipt['command'])
        receipt['exit_code'] = 0
        saved = progress.save(binding, receipt, receipt['command'])
        self.assertTrue(valid_success(saved, binding))
        self.assertEqual(progress.lookup(binding), saved)

    def test_groups_are_bounded_and_pure_scan_work_is_coalesced(self):
        observations = TemporalInputs()
        actual = self.run_group(tuple('N' + str(n) for n in range(17)), observations)
        self.assertEqual([len(items) for items in self.calls], [8, 8, 1])
        self.assertEqual(len(actual), 17)
        self.assertLess(observations.scan_count, 40)
        before = observations.scan_count
        self.runner.verify_tasks(self.plan, [self.task('N' + str(n)) for n in range(17)],
                                 actual, {}, observations)
        self.assertLessEqual(observations.scan_count - before, 3)

    def test_batch_command_cannot_select_arbitrary_driver_or_multi_origin_item(self):
        for modify in (lambda t: t['command'].__setitem__(2, 'untrusted'),
                       lambda t: t.update(modules=['A', 'B']),
                       lambda t: t['command'].__setitem__(0, '/bin/sh')):
            task = self.task('A')
            modify(task)
            with self.assertRaises(ValueError):
                check_group([task], self.runtime)


class ReflectionPathTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='reflection-paths-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()

    def graph(self):
        package = self.root / 'package'
        package.mkdir()
        for name in ('Init', 'Quartz.A', 'Quartz.B'):
            source = package / (name.replace('.', '/') + '.lean')
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text('module\n')
            fixtures.native_fixture(package, name)
        earlier = self.root / 'earlier/.lake/build/lib/lean'
        earlier.mkdir(parents=True)
        library = package / '.lake/build/lib/lean'
        inputs = CheckInputs(TemporalInputs())
        graph = ReflectionGraph(package, [str(earlier), str(library)],
                                {'installation': str(self.root / 'compiler')}, inputs)
        return graph, inputs, earlier, library

    def test_cached_paths_keep_intermediate_symlink_checks_eager(self):
        first, second = self.root / 'first', self.root / 'second'
        first.mkdir()
        second.mkdir()
        (first / 'input').write_bytes(b'stable shared inode')
        os.link(first / 'input', second / 'input')
        link = self.root / 'selected'
        link.symlink_to(first, target_is_directory=True)
        path = link / 'input'
        observations = TemporalInputs()
        observations.hash_file(path)
        stamp = observations.stamp(path)
        eager = False
        with self.assertRaises(InputDrift):
            with observations.inspection():
                link.unlink()
                link.symlink_to(second, target_is_directory=True)
                self.assertEqual(observations.stamp(path), stamp)
                try:
                    observations.hash_file(path)
                except InputDrift:
                    eager = True
                    raise
        self.assertTrue(eager)

    def test_namespace_probes_are_shared_but_all_candidates_remain_guarded(self):
        graph, inputs, earlier, library = self.graph()
        with patch.object(inputs, 'observe_resolution', wraps=inputs.observe_resolution) as observe:
            with inputs.inspection():
                result = graph.closure(['Quartz.A', 'Quartz.B'])
        self.assertIsNotNone(result)
        paths = [call.args[0] for call in observe.call_args_list]
        self.assertEqual(len(paths), len(set(paths)))
        for parent in (earlier, library):
            for name in ('Quartz', 'Quartz.olean', 'Init', 'Init.olean'):
                self.assertIn(parent / name, inputs.native.resolution)
        inputs.assert_stable()

    def test_cached_namespace_shadow_cannot_escape_the_binding_boundary(self):
        graph, inputs, earlier, _ = self.graph()
        escaped = []
        with self.assertRaises(InputDrift):
            with inputs.inspection():
                graph.node('Quartz.A')
                (earlier / 'Quartz').mkdir()
                graph.node('Quartz.B')
            escaped.append('binding consumed')
        self.assertEqual(escaped, [])
        # The next interval must resolve afresh. An empty earlier namespace
        # wins over the complete later library and disables reflective reuse.
        fresh = ReflectionGraph(graph.root, graph.search_path, graph.toolchain,
                                CheckInputs(inputs.whole))
        self.assertIsNone(fresh.closure(['Quartz.A']))

    def test_compiler_library_alias_retains_physical_provenance_and_drift_guard(self):
        graph, inputs, _, library = self.graph()
        compiler = self.root / 'compiler/lib/lean'
        compiler.mkdir(parents=True)
        for source in library.glob('Init.*'):
            source.rename(compiler / source.name)
        alias = self.root / 'compiler-alias'
        alias.symlink_to(compiler, target_is_directory=True)
        graph = ReflectionGraph(graph.root, [str(library), str(alias)], graph.toolchain, inputs)
        replacement = self.root / 'other-compiler'
        replacement.mkdir()
        for source in compiler.iterdir():
            os.link(source, replacement / source.name)
        with inputs.inspection():
            value = graph.node('Init')
        self.assertEqual(value['owner'], 'compiler-installation')
        alias.unlink()
        alias.symlink_to(replacement, target_is_directory=True)
        with self.assertRaises(InputDrift):
            inputs.assert_stable()


if __name__ == '__main__':
    unittest.main()
