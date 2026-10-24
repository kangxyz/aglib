"""Native local command orchestration fixtures; no compiler or network is run.

Native files and process receipts below are synthetic. They exercise the actual
input bindings and reflection graph, but provide no Lean compilation evidence.
"""
from contextlib import redirect_stderr, redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from lean_tools import cli, local, resources
from lean_tools.local import _prepare_auditor
from lean_tools.runtime import CommandFailed
from lean_tools.state import TemporalInputs, read_json, write_json


CHECK = ('python3', 'scripts/check_sources.py')


def native_fixture(root, name, imports=()):
    relative = name.replace('.', '/')
    source = root / (relative + '.lean')
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text('module\n' + ''.join('import ' + item + '\n' for item in imports))
    library = root / '.lake/build/lib/lean'
    for suffix in ('.olean', '.ilean', '.c'):
        directory = root / '.lake/build/ir' if suffix == '.c' else library
        artifact = directory / (relative + suffix)
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.write_bytes(('synthetic ' + name + suffix).encode())
    write_json(library / (relative + '.ilean'), {
        'version': 5, 'module': name,
        'directImports': [[item, False, False, False] for item in imports]})
    write_json(library / (relative + '.trace'), {
        'schemaVersion': '2025-09-10', 'depHash': '0' * 16,
        'outputs': {'m': False, 'o': '0' * 16 + '.olean',
                    'i': '0' * 16 + '.ilean', 'c': '0' * 16 + '.c'}})


class FakeRuntime:
    """Explicit injected executor, with exact command/receipt and failure controls."""
    def __init__(self, root):
        self.root = root
        self.environment = {}
        self.resource_config = resources.ResourceConfig()
        self.toolchain = {'lean': 'synthetic-lean', 'lake': 'synthetic-lake',
                          'installation': str(root / '.lake/synthetic-toolchain')}
        self.calls = []
        self.fail = None
        self.receipt_change = None
        self.callback = None
        self.compiler_calls = 0

    def compiler_identity(self, hash_file):
        self.compiler_calls += 1
        return dict(self.toolchain)

    def run(self, task, directory):
        command = task['command']
        self.calls.append(command)
        if self.fail and self.fail(command):
            raise CommandFailed('Synthetic native command failed', 1)
        if '-o' in command:
            Path(command[command.index('-o') + 1]).write_text('"2026-03-17"\n')
        if self.callback:
            self.callback(command)
        receipt = {'state': 'completed', 'command': list(command), 'cwd': task['cwd'],
                   'exit_code': 0, 'guard_failure': None, 'owned_group_gone': True}
        if self.receipt_change:
            receipt.update(self.receipt_change)
        return {'receipt': receipt}


class NativeFixture(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='native-local-', dir='/private/tmp')
        self.addCleanup(temporary.cleanup)
        self.scratch = Path(temporary.name).resolve()
        self.root = self.scratch / 'package'
        self.root.mkdir()
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:synthetic\n')
        (self.root / 'lakefile.toml').write_text('name = "quartz"\ndefaultTargets = ["Quartz"]\n')
        native_fixture(self.root, 'Init')
        native_fixture(self.root, 'Quartz.Base')
        native_fixture(self.root, 'Quartz', ['Quartz.Base'])
        native_fixture(self.root, 'Batteries.Tactic.Lint')
        checker = self.root / 'scripts/check_sources.py'
        checker.parent.mkdir()
        checker.write_text('# synthetic source checker\n')
        self.mathlib = self.root / '.lake/packages/mathlib'
        native_fixture(self.mathlib, 'Mathlib.EntryChecks')
        native_fixture(self.mathlib, 'Mathlib.TextChecks')
        self.helper_sources, self.helper_binaries = {}, {}
        for name, module in (('mk_all', 'Mathlib.EntryChecks'),
                             ('lint-style', 'Mathlib.TextChecks')):
            helper = self.mathlib / 'scripts' / (name + '.lean')
            helper.parent.mkdir(parents=True, exist_ok=True)
            helper.write_text('module\nimport ' + module + '\n')
            binary = self.mathlib / '.lake/build/bin' / name
            binary.parent.mkdir(parents=True, exist_ok=True)
            binary.write_bytes(('synthetic ' + name).encode())
            self.helper_sources[name], self.helper_binaries[name] = helper, binary
        self.auditor = self.root / '.lake/axiom-audit/.lake/build/bin/axiom-audit'
        self.auditor.parent.mkdir(parents=True)
        self.auditor.write_bytes(b'synthetic pinned upstream auditor')
        self.runtime = FakeRuntime(self.root)
        self.state = self.scratch / 'state'
        self.progress = self.scratch / 'progress'
        self.outputs = self.scratch / 'accepted.jsonl'
        self.actual_check_output = subprocess.check_output
        self.addCleanup(patch.stopall)
        patch('lean_tools.local.subprocess.check_output', side_effect=self.check_output).start()
        patch('lean_tools.local._prepare_auditor', side_effect=self.prepare_auditor).start()

    def check_output(self, command, **kwargs):
        if command == ['lake', 'env', 'printenv', 'LEAN_PATH']:
            return os.pathsep.join(str(root / '.lake/build/lib/lean')
                                   for root in (self.root, self.mathlib)) + '\n'
        return self.actual_check_output(command, **kwargs)

    def prepare_auditor(self, root, runtime, directory, observations):
        observations.hash_file(self.auditor)
        return self.auditor

    def check(self, **options):
        arguments = dict(source_checks=[CHECK], state=self.state, progress=self.progress,
                         runtime=self.runtime)
        arguments.update(options)
        return local.check(self.root, ['Quartz'], **arguments)

    def records(self):
        return [read_json(path) for path in self.progress.glob('*.json')]

    def summaries(self):
        return [read_json(path) for path in self.state.glob('run-*/result.json')]


class NativeFlowTests(NativeFixture):
    def test_prepared_gitless_package_runs_only_required_native_commands(self):
        self.assertFalse((self.root / '.git').exists())
        result = self.check(check_targets=['AglibTest'], outputs=self.outputs)
        calls = self.runtime.calls
        self.assertEqual(calls[0], list(CHECK))
        self.assertEqual(calls[1][:4], ['lake', '--rehash', 'build', 'Quartz'])
        self.assertEqual(calls[1][-2], '-o')
        self.assertEqual(calls[2], ['lake', '--rehash', 'build', 'batteries/runLinter',
                                  'mathlib/lint-style', 'mathlib/mk_all', 'AglibTest'])
        self.assertEqual(calls[3:], [
            ['lake', '--no-build', 'exe', 'mathlib/mk_all', '--lib', 'Quartz', '--check'],
            ['lake', '--no-build', 'exe', 'mathlib/lint-style', 'Quartz'],
            ['lake', 'test'],
            ['lake', '--no-build', 'lint', 'Quartz', '--', '--trace'],
            ['lake', 'env', str(self.auditor), '--root', 'Quartz']])
        self.assertEqual(result['status'], 'complete')
        self.assertEqual(self.runtime.compiler_calls, 1)
        self.assertTrue(self.outputs.is_file())
        self.assertEqual(self.outputs.read_text(), '"2026-03-17"\n')
        self.assertFalse(any(self.state.rglob('plan.json')))
        self.assertFalse(any(self.state.rglob('complete.json')))

    def test_nonempty_documentation_diff_runs_static_checks_without_lean_discovery(self):
        with patch.object(local, 'changed_paths', return_value=['docs/guide.md']):
            result = self.check(outputs=self.outputs)
        self.assertFalse(result['native'])
        self.assertEqual(self.runtime.calls, [list(CHECK)])
        self.assertEqual(self.runtime.compiler_calls, 0)
        self.assertFalse(self.outputs.exists())

    def test_clean_or_full_requests_keep_native_checks(self):
        for full in (False, True):
            with self.subTest(full=full), patch.object(local, 'changed_paths', return_value=[]):
                self.assertTrue(self.check(full=full)['native'])
        self.assertEqual(self.runtime.compiler_calls, 2)
        self.assertEqual(self.runtime.calls.count(['lake', 'test']), 2)

    def test_source_only_is_explicit_and_full_range_conflicts_are_rejected(self):
        result = self.check(source_only=True)
        self.assertFalse(result['native'])
        self.assertEqual(self.runtime.calls, [list(CHECK)])
        self.assertEqual(self.runtime.compiler_calls, 0)
        with self.assertRaisesRegex(ValueError, 'full'):
            self.check(full=True, base='HEAD')

    def test_source_only_with_native_outputs_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'outputs|mapping|source'):
            self.check(source_only=True, outputs=self.outputs)
        self.assertFalse(self.outputs.exists())
        self.assertEqual(self.runtime.calls, [])
        self.assertEqual(self.runtime.compiler_calls, 0)

    def test_late_checker_native_mutation_prevents_success_and_output_export(self):
        artifact = self.root / '.lake/build/lib/lean/Batteries/Tactic/Lint.olean'
        lint = ['lake', '--no-build', 'lint', 'Quartz', '--', '--trace']
        audit = ['lake', 'env', str(self.auditor), '--root', 'Quartz']
        self.outputs.write_text('previous compatible export\n')

        def mutate_later(command):
            if command == audit:
                artifact.write_bytes(b'changed checker-only native artifact')

        self.runtime.callback = mutate_later
        with self.assertRaises(ValueError):
            self.check(outputs=self.outputs)
        self.assertEqual(self.runtime.calls.count(lint), 1)
        self.assertEqual(self.runtime.calls.count(audit), 1)
        self.assertEqual(self.outputs.read_text(), 'previous compatible export\n')
        self.assertEqual([summary['status'] for summary in self.summaries()], ['failed'])

    def test_empty_production_is_rejected_before_state_or_execution(self):
        with self.assertRaisesRegex(ValueError, 'production root'):
            local.check(self.root, [], runtime=self.runtime, state=self.state)
        self.assertEqual(self.runtime.calls, [])
        self.assertFalse(self.state.exists())

    def test_failed_check_never_exports_mapping_or_reports_complete(self):
        self.runtime.fail = lambda command: command[:3] == ['lake', '--no-build', 'lint']
        with self.assertRaisesRegex(ValueError, 'Synthetic native command failed'):
            self.check(outputs=self.outputs)
        self.assertFalse(self.outputs.exists())
        self.assertEqual([s['status'] for s in self.summaries()], ['failed'])
        self.assertNotIn('lint', [r['binding']['kind'] for r in self.records()])

    def test_runtime_receipt_guards_prevent_false_source_success(self):
        for invalid in ({'exit_code': 1}, {'guard_failure': 'rss-limit'},
                        {'owned_group_gone': False}, {'state': 'running'},
                        {'command': ['different']}, {'cwd': str(self.scratch)}):
            with self.subTest(receipt=invalid):
                self.runtime.receipt_change = invalid
                with self.assertRaisesRegex(ValueError, 'receipt'):
                    self.check(source_only=True)
        self.assertEqual(self.records(), [])
        self.assertTrue(all(s['status'] == 'failed' for s in self.summaries()))

    def test_mutation_during_source_check_is_not_saved_as_success(self):
        self.runtime.callback = lambda command: (self.root / 'Quartz.lean').write_text('changed\n')
        with self.assertRaises(ValueError):
            self.check(source_only=True)
        self.assertEqual(self.records(), [])


class AuditorPreparationTests(NativeFixture):
    def prepare_checkout(self):
        tool = self.root / '.lake/axiom-audit'
        (tool / '.git').mkdir()
        (tool / 'lean-toolchain').write_bytes((self.root / 'lean-toolchain').read_bytes())
        self.auditor.chmod(0o755)
        return tool

    def test_prepared_upstream_auditor_uses_pinned_revision_and_native_build(self):
        tool = self.prepare_checkout()
        observations = TemporalInputs()
        with patch('lean_tools.local.subprocess.check_output', side_effect=[local.AUDITOR_REVISION + '\n', b'']):
            result = _prepare_auditor(self.root, self.runtime, self.scratch / 'auditor', observations)
        self.assertEqual(result, self.auditor)
        self.assertEqual(self.runtime.calls, [['lake', '--rehash', 'build']])
        self.assertTrue(tool.is_relative_to(self.root / '.lake'))

    def test_dirty_pinned_auditor_sources_are_rejected(self):
        self.prepare_checkout()
        with patch('lean_tools.local.subprocess.check_output',
                   side_effect=[local.AUDITOR_REVISION + '\n', b'AxiomAudit/Main.lean\n']):
            with self.assertRaisesRegex(ValueError, 'local modifications'):
                _prepare_auditor(self.root, self.runtime, self.scratch / 'auditor', TemporalInputs())
        self.assertEqual(self.runtime.calls, [])

    def test_wrong_auditor_revision_blocks_execution(self):
        self.prepare_checkout()
        with patch('lean_tools.local.subprocess.check_output', return_value='0' * 40 + '\n'):
            with self.assertRaisesRegex(ValueError, 'revision'):
                _prepare_auditor(self.root, self.runtime, self.scratch / 'auditor', TemporalInputs())
        self.assertEqual(self.runtime.calls, [])

    def test_explicit_auditor_with_wrong_toolchain_is_rejected(self):
        tool = self.prepare_checkout()
        (tool / 'lean-toolchain').write_text('wrong compiler\n')
        self.runtime.environment['LEAN_CI_AUDITOR_ROOT'] = str(tool)
        with patch('lean_tools.local.subprocess.check_output', side_effect=[local.AUDITOR_REVISION + '\n', b'']):
            with self.assertRaisesRegex(ValueError, 'toolchain'):
                _prepare_auditor(self.root, self.runtime, self.scratch / 'auditor', TemporalInputs())
        self.assertEqual(self.runtime.calls, [])


class CommandInterfaceTests(unittest.TestCase):
    def test_cli_lists_native_commands_without_plan_or_compiler(self):
        output = io.StringIO()
        with redirect_stdout(output):
            code = cli.main(['check', '--list'], root='/private/tmp', production=['Quartz'],
                            check_targets=['QuartzTest'], source_checks=[CHECK], environment={})
        self.assertEqual(code, 0)
        commands = [json.loads(line) for line in output.getvalue().splitlines()]
        self.assertEqual(commands[0], list(CHECK))
        self.assertIn(['lake', 'test'], commands)
        self.assertEqual(commands[-1], ['lake', 'env', '<pinned-axiom-audit>', '--root', 'Quartz'])
        self.assertEqual(len(commands), 8)

    def test_cli_has_no_implicit_empty_production_success(self):
        with tempfile.TemporaryDirectory(dir='/private/tmp') as root, redirect_stderr(io.StringIO()):
            self.assertEqual(cli.main(['check', '--list'], root=root, environment={}), 1)

    def test_documentation_optimization_requires_nonempty_safe_diff(self):
        self.assertFalse(local.documentation_only([]))
        self.assertTrue(local.documentation_only(['docs/a.md', 'README.md']))
        for names in (['Quartz.lean'], ['scripts/readme.md'], ['.github/change.md'],
                      ['README.md', 'lakefile.toml']):
            self.assertFalse(local.documentation_only(names))


if __name__ == '__main__':
    unittest.main()
