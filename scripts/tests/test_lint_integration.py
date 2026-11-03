"""Packaged lint dispatch, observed checker inputs and resource admission."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest
from unittest.mock import patch

from lean_tools import __version__, lint, resources
from lean_tools.state import InputDrift
from test_shared import NativeFixture, native_fixture


class LintInputTests(NativeFixture):
    def setUp(self):
        super().setUp()
        assets = self.scratch / 'installed-adapter'
        shutil.copytree(lint.ASSETS, assets)
        patch('lean_tools.lint.ASSETS', assets).start()
        self.private = self.root / '.lake/lint-runner'

        def prepare(command):
            if command != lint.command(prepare=True):
                return
            self.private.mkdir(parents=True, exist_ok=True)
            for name, content in (
                    ('BatchedLint.lean', (assets / 'BatchedLint.lean').read_bytes()),
                    ('lakefile.toml', b'fixed generated configuration\n'),
                    ('lean-toolchain', b'leanprover/lean4:synthetic\n'),
                    ('.lake/build/bin/batchedLint', b'compiled:' + hashlib.sha256(
                        (assets / 'BatchedLint.lean').read_bytes()).digest())):
                path = self.private / name
                path.parent.mkdir(parents=True, exist_ok=True)
                if not path.exists() or path.read_bytes() != content:
                    path.write_bytes(content)
            (self.private / 'lake-manifest.json').write_text('{"generated": true}\n')
        self.prepare = prepare
        self.runtime.callback = prepare

    def test_prepared_checker_runs_again_without_storing_lint_success(self):
        self.check()
        self.assertTrue((self.private / '.lake/build/bin/batchedLint').is_file())
        self.assertEqual(self.check()['performed_checks'], ['lint'])
        self.assertNotIn('lint', [r['binding']['kind'] for r in self.records()])

    def test_adapter_and_provider_changes_invalidate_only_lint(self):
        self.check()
        for path in (lint.ASSETS / 'run.sh', lint.ASSETS / 'preflight.py',
                     lint.ASSETS / 'BatchedLint.lean',
                     self.batteries / 'scripts/runLinter.lean',
                     self.batteries / 'lakefile.toml'):
            with self.subTest(path=path):
                comment = '--' if path.suffix == '.lean' else '#'
                path.write_text(path.read_text() + '\n' + comment + ' changed checker input\n')
                self.assertEqual(self.check()['performed_checks'], ['lint'])

    def test_all_configured_driver_roots_are_reflected(self):
        native_fixture(self.root, 'Quartz.Extra')
        path = self.root / 'lakefile.toml'
        path.write_text(path.read_text().replace('["--no-build", "Quartz"]',
                                                '["--no-build", "Quartz", "Quartz.Extra"]'))
        self.check()
        self.auditor.write_bytes(b'force later audit execution')
        audit = ['lake', 'env', str(self.auditor), '--root', 'Quartz']
        def mutate(command):
            self.prepare(command)
            if command == audit:
                (self.root / '.lake/build/lib/lean/Quartz/Extra.olean').write_bytes(
                    b'changed driver-only input during audit')
        self.runtime.callback = mutate
        with self.assertRaises((InputDrift, ValueError)):
            self.check(outputs=self.outputs)
        self.assertFalse(self.outputs.exists())

    def test_late_generated_checker_mutation_is_rejected(self):
        audit = ['lake', 'env', str(self.auditor), '--root', 'Quartz']
        for name in ('.lake/build/bin/batchedLint', 'lake-manifest.json'):
            with self.subTest(name=name):
                self.auditor.write_bytes(b'changed auditor forces execution: ' + name.encode())
                def mutate(command):
                    self.prepare(command)
                    if command == audit:
                        path = self.private / name
                        path.write_bytes(path.read_bytes() + b'changed during later audit')
                self.runtime.callback = mutate
                with self.assertRaises((InputDrift, ValueError)):
                    self.check(outputs=self.outputs)
                self.assertFalse(self.outputs.exists())

    def test_mutation_during_lint_never_records_success(self):
        def mutate(command):
            self.prepare(command)
            if command == lint.command(['Quartz']):
                path = lint.ASSETS / 'BatchedLint.lean'
                path.write_text(path.read_text() + '\n-- late source mutation\n')
        self.runtime.callback = mutate
        with self.assertRaises((InputDrift, ValueError)):
            self.check(outputs=self.outputs)
        self.assertNotIn('lint', [r['binding']['kind'] for r in self.records()])

    def test_unsupported_context_never_reuses_an_unknown_scope(self):
        with patch('lean_tools.lint.supported_provider', return_value=False):
            self.check()
            self.assertIn('lint', self.check()['performed_checks'])

    def test_failed_preparation_keeps_independent_feedback_and_no_export(self):
        self.runtime.fail = lambda c: c == lint.command(prepare=True)
        with self.assertRaisesRegex(ValueError, 'lint-preparation'):
            self.check(outputs=self.outputs)
        self.assertNotIn(lint.command(['Quartz']), self.runtime.calls)
        self.assertIn(['lake', 'test'], self.runtime.calls)
        self.assertIn(['lake', 'env', str(self.auditor), '--root', 'Quartz'], self.runtime.calls)
        self.assertFalse(self.outputs.exists())


class PackagedAdapterTests(unittest.TestCase):
    def test_declared_package_data_and_version_are_complete(self):
        root = Path(__file__).resolve().parents[1]
        config = tomllib.loads((root / 'pyproject.toml').read_text())
        self.assertEqual(config['project']['version'], __version__)
        patterns = config['tool']['setuptools']['package-data']['lean_tools']
        for name in ('run.sh', 'preflight.py', 'BatchedLint.lean'):
            self.assertTrue(any((root / 'lean_tools' / '_lint' / name).match(p) for p in patterns))

    def test_copied_install_dispatches_from_unrelated_checkout_without_github(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            installation = base / 'installation'
            shutil.copytree(Path(lint.__file__).parent, installation / 'lean_tools',
                            ignore=shutil.ignore_patterns('__pycache__'))
            root = base / 'unrelated'; root.mkdir()
            (root / 'lakefile.toml').write_text('name = "Aglib"\n')
            binary = base / 'bin'; binary.mkdir()
            lake = binary / 'lake'
            lake.write_text('#!/bin/sh\nprintf "%s\\n" "$*"\nexit 23\n')
            lake.chmod(0o755)
            env = dict(os.environ, PYTHONPATH=str(installation),
                       PATH=str(binary) + os.pathsep + os.environ['PATH'])
            plan = subprocess.check_output([sys.executable, '-m', 'lean_tools', 'check',
                '--root', str(root), '--list'], env=env, cwd=root, text=True)
            commands = [json.loads(line) for line in plan.splitlines()]
            actual = next(c for c in commands if c[0] == 'bash' and c[-1] == 'Aglib')
            self.assertTrue(Path(actual[1]).is_relative_to(installation.resolve()))
            self.assertFalse((root / '.github').exists())
            result = subprocess.run(actual, cwd=root, env=env, text=True, capture_output=True)
            self.assertEqual(result.returncode, 23)
            self.assertEqual(result.stdout.strip(), '--no-build lint Aglib -- --trace')


class LintResourceTests(unittest.TestCase):
    def test_guard_injects_authoritative_per_process_cap(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / 'env.json'
            command = [sys.executable, '-c', 'import json,os;json.dump(dict(os.environ),open('
                       + repr(str(output)) + ',"w"))']
            budget = {'lean_threads': 1, 'max_active_lean': 1, 'lean_memory_mb': 64,
                      'rss_limit_mb': 256, 'sample_seconds': 0.001}
            env = dict(os.environ, LEAN_TOOLS_LINT_MAX_THREADS='99', CI_LINT_WORKERS='8')
            self.assertEqual(resources.run(command, env=env, budget=budget, sampler=lambda _: []), 0)
            captured = json.loads(output.read_text())
            self.assertEqual(captured['LEAN_TOOLS_LINT_MAX_THREADS'], '1')
            self.assertEqual(captured['LEAN_NUM_THREADS'], '1')


if __name__ == '__main__':
    unittest.main()
