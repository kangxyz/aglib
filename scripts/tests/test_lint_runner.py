"""Native full-predicate comparison; AGLIB_LINT_BATTERIES selects the pinned sources.

Only tiny fixture roots and the pinned runner target are built. No Aglib/Mathlib
build or toolchain download is performed. Backend probes call batching directly.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import tomllib
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
HELPER = ROOT / "scripts/lean_tools/_lint"
FIXTURES = ROOT / "scripts/tests/fixtures/lint"
spec = importlib.util.spec_from_file_location("lint_preflight", HELPER / "preflight.py")
preflight = importlib.util.module_from_spec(spec)
spec.loader.exec_module(preflight)


class PreflightTests(unittest.TestCase):
    def test_only_supported_full_no_build_configuration_is_adapted(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "dep").mkdir()
            (root / "dep/runtime.lean").write_text("pinned")
            config = ('lintDriver = "batteries/runLinter"\n'
                'lintDriverArgs = ["--no-build", "Fixture"]\nbuiltinLint = true\n')
            (root / "lakefile.toml").write_text(config)
            (root / "lake-manifest.json").write_text(json.dumps({"packages": [
                {"name": "batteries", "type": "path", "dir": "dep"}]}))
            with patch.object(preflight, "SOURCES", {"runtime.lean":
                    hashlib.sha256(b"pinned").hexdigest()}):
                self.assertTrue(preflight.supported(root))
                for variant in (config.replace("true", "false"),
                        config.replace("builtinLint = true\n", ""),
                        config.replace('"--no-build", ', ''),
                        config.replace('"--no-build"', '"--update"'),
                        config.replace('"batteries/runLinter"', '"custom"')):
                    (root / "lakefile.toml").write_text(variant)
                    self.assertFalse(preflight.supported(root))
                (root / "lakefile.toml").write_text(config)
                (root / "dep/runtime.lean").write_text("incompatible API")
                self.assertFalse(preflight.supported(root))
                (root / "dep/runtime.lean").write_text("pinned")
                (root / "lakefile.lean").write_text("active Lean configuration")
                self.assertFalse(preflight.supported(root))

    def test_unsupported_fallback_retains_original_thread_environment(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "bin").mkdir()
            fake = root / "bin/lake"
            fake.write_text('#!/usr/bin/env python3\nimport json,os,sys\n'
                'print(json.dumps({"args":sys.argv[1:],"threads":os.environ.get("LEAN_NUM_THREADS")}))\n')
            fake.chmod(0o755)
            env = dict(os.environ, LEAN_NUM_THREADS="1", CI_LINT_WORKERS="4")
            env["PATH"] = str(root / "bin") + os.pathsep + os.environ["PATH"]
            result = subprocess.run(["bash", str(HELPER / "run.sh"), "Fixture"],
                cwd=root, env=env, text=True, capture_output=True, check=True)
            record = json.loads(result.stdout)
            self.assertEqual(record["threads"], "1")
            self.assertEqual(record["args"], ["--no-build", "lint", "Fixture", "--", "--trace"])


class PrivatePreparationTests(unittest.TestCase):
    """The strict preparation switch is tested with no native compiler."""

    def run_adapter(self, *, strict=False, missing=False, builtin_status=0):
        with tempfile.TemporaryDirectory(prefix='lint-private-preparation-') as temp:
            root = Path(temp)
            helper = root / 'helper'
            helper.mkdir()
            shutil.copyfile(HELPER / 'run.sh', helper / 'run.sh')
            (helper / 'BatchedLint.lean').write_text('-- shell fixture only\n')
            provider = root / 'resolved provider'
            provider.mkdir()
            (helper / 'preflight.py').write_text(
                'import sys\nprint(' + repr(str(provider)) +
                ' if sys.argv[1] == "--batteries-dir" else "fixture-driver-args")\n')
            binary = root / 'bin'
            binary.mkdir()
            lake = binary / 'lake'
            lake.write_text('''#!/usr/bin/env python3
import json,os,sys
from pathlib import Path
a=sys.argv[1:]
with open(os.environ['TRACE'],'a') as f:f.write(json.dumps(a)+'\\n')
if a==['env','lean','--version']:print('Lean (version 4.34.1, fixture)')
elif a and a[0]=='--dir':
    if '--no-build' in a and os.environ['MISSING_RUNNER']=='1':sys.exit(23)
    p=Path(a[1])/'.lake/build/bin';p.mkdir(parents=True,exist_ok=True)
    (p/'batchedLint').write_text('fixture executable')
elif '--builtin-only' in a:sys.exit(int(os.environ['BUILTIN_STATUS']))
''')
            lake.chmod(0o755)
            trace = root / 'trace'
            env = dict(os.environ, PATH=str(binary)+os.pathsep+os.environ['PATH'],
                       TRACE=str(trace), MISSING_RUNNER=str(int(missing)),
                       BUILTIN_STATUS=str(builtin_status), CI_LINT_NO_BUILD=strict and 'true' or 'false')
            result = subprocess.run(['bash', str(helper / 'run.sh'), 'Fixture', 'Other'],
                                    cwd=root, env=env, text=True, capture_output=True)
            calls = [json.loads(line) for line in trace.read_text().splitlines()]
            config = tomllib.loads((root / '.lake/lint-runner/lakefile.toml').read_text())
            return result, calls, config, str(provider)

    def test_default_private_build_and_provider_resolution_are_unchanged(self):
        result, calls, config, provider = self.run_adapter(missing=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        private = next(a for a in calls if a[:1] == ['--dir'])
        self.assertEqual(private[2:], ['--file','lakefile.toml','--update','--keep-toolchain','build','batchedLint'])
        self.assertEqual(config['require'][0]['path'], provider)
        self.assertEqual(config['lean_exe'][0]['root'], 'BatchedLint')

    def test_strict_private_build_only_adds_no_build_and_keeps_both_predicates(self):
        result, calls, config, provider = self.run_adapter(strict=True, builtin_status=1)
        self.assertEqual(result.returncode, 1, result.stderr)
        private = next(a for a in calls if a[:1] == ['--dir'])
        self.assertEqual(private[2:], ['--file','lakefile.toml','--update','--keep-toolchain','--no-build','build','batchedLint'])
        self.assertEqual(config['require'][0]['path'], provider)
        self.assertIn(['--no-build','--builtin-only','lint','Fixture','Other'], calls)
        self.assertTrue(any(a[:1] == ['env'] and a[-1] == 'fixture-driver-args' for a in calls))

    def test_strict_missing_private_output_fails_before_checks_without_fallback(self):
        result, calls, _, _ = self.run_adapter(strict=True, missing=True)
        self.assertEqual(result.returncode, 23, result.stderr)
        self.assertEqual(len([a for a in calls if a[:1] == ['--dir']]), 1)
        self.assertFalse(any('--builtin-only' in a or a == ['--no-build','lint','Fixture','Other','--','--trace'] for a in calls))
        self.assertFalse(any(a[:1] == ['env'] and a[-1] == 'fixture-driver-args' for a in calls))


@unittest.skipUnless(os.environ.get("AGLIB_LINT_BATTERIES"), "set AGLIB_LINT_BATTERIES")
class NativeRunnerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.batteries = Path(os.environ["AGLIB_LINT_BATTERIES"]).resolve()
        cls.lake = os.environ.get("AGLIB_LINT_LAKE", shutil.which("lake"))
        if not cls.lake:
            raise unittest.SkipTest("matching Lake unavailable")
        cls.env = dict(os.environ, LEAN_ABORT_ON_PANIC="1", LEAN_NUM_THREADS="1")
        cls.env["PATH"] = str(Path(cls.lake).parent) + os.pathsep + os.environ["PATH"]
        if os.environ.get("AGLIB_LINT_MATHLIB_SOURCES"):
            cls.env["LEAN_SRC_PATH"] = os.environ["AGLIB_LINT_MATHLIB_SOURCES"]
        cls.base = tempfile.TemporaryDirectory(prefix="lint-runner-",
            dir=os.environ.get("AGLIB_LINT_TEST_TMP"))

    @classmethod
    def tearDownClass(cls):
        cls.base.cleanup()

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir=self.base.name)
        self.root = Path(self.temp.name)
        shutil.copytree(FIXTURES / "Fixture", self.root / "Fixture")
        shutil.copyfile(FIXTURES / "Fixture.lean", self.root / "Fixture.lean")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
        (self.root / "lakefile.toml").write_text(
            'name = "Fixture"\nlintDriver = "batteries/runLinter"\n'
            'lintDriverArgs = ["--no-build", "Fixture"]\nbuiltinLint = true\n'
            '[[lean_lib]]\nname = "Fixture"\n[[require]]\nname = "batteries"\n'
            'path = ' + json.dumps(str(self.batteries)) + '\n')
        self.build()
        self.assertTrue(preflight.supported(self.root))

    def tearDown(self):
        self.temp.cleanup()

    def command(self, args, code=0, extra_env=None):
        env = dict(self.env, **(extra_env or {}))
        result = subprocess.run(args, cwd=self.root, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=90)
        self.assertEqual(result.returncode, code, result.stdout)
        return result.stdout

    def build(self, *roots):
        self.command([self.lake, "build", "batteries/runLinter", *(roots or ("+Fixture",))])

    def native(self, code=0, roots=("Fixture",)):
        return self.command([self.lake, "--no-build", "lint", *roots, "--", "--trace"], code)

    def batched(self, code=0, roots=("Fixture",), workers=2):
        return self.command(["bash", str(HELPER / "run.sh"), *roots], code,
            {"CI_LINT_WORKERS": str(workers)})

    def append(self, name, text):
        path = self.root / name
        path.write_text(path.read_text() + text)
        self.build()

    def test_every_invocation_and_everyday_edit_runs_all_checks(self):
        self.native()
        for workers in (1, 2, 4):
            output = self.batched(workers=workers)
            self.assertIn("3 declarations, 9 linters", output)
            self.assertIn("Completed linting!", output)
            self.assertIn("import elapsed=", output)
        self.append("Fixture/Right.lean", "\n-- An everyday edit.\n")
        self.assertIn("3 declarations, 9 linters", self.batched())
        self.assertIn("3 declarations, 9 linters", self.batched())
        self.assertFalse((self.root / ".lake/build/ci-lint").exists())

    def test_failures_nolints_and_suppression_attributes_match_native(self):
        self.append("Fixture/Left.lean", '\nnamespace Fixture\n'
            'public theorem localTaut : True = True := rfl\nend Fixture\n')
        self.assertIn("LHS equals RHS syntactically", self.native(1))
        self.assertIn("LHS equals RHS syntactically", self.batched(1))
        (self.root / "scripts").mkdir()
        suppressions = self.root / "scripts/nolints.json"
        suppressions.write_text(json.dumps([["synTaut", "Fixture.localTaut"]]))
        self.native()
        self.assertIn("synTaut: 1", self.batched())
        suppressions.unlink()
        self.native(1)
        self.batched(1)
        path = self.root / "Fixture/Left.lean"
        path.write_text(path.read_text().replace('public theorem localTaut',
            '@[nolint synTaut] public theorem localTaut'))
        self.build()
        self.native()
        self.batched()
        suppressions.write_text("invalid JSON")
        self.native(1)
        self.batched(1)

    def test_local_check_reruns_custom_linter_external_state(self):
        from lean_tools import lint, local
        from lean_tools.runtime import CommandFailed
        from test_shared import FakeRuntime

        self.append("Fixture/Left.lean", '\nopen Lean\n'
            '/-- A custom linter whose input is outside the Lean graph. -/\n'
            '@[env_linter] public meta def customExternalCheck : Batteries.Tactic.Lint.Linter where\n'
            '  noErrorsFound := "ok"\n  errorsFound := "failed"\n'
            '  test decl := do\n    if decl != `Fixture.leftValue then return none\n'
            '    let state ← IO.FS.readFile "lint-external-state"\n'
            '    if state == "fail" then return m!"external linter failure"\n'
            '    return none\n')
        external = self.root / "lint-external-state"
        external.write_text("pass")
        owner = self

        class LintRuntime(FakeRuntime):
            """Execute real lint; unrelated final-check phases use test receipts."""
            def run(self, task, directory):
                command = task['command']
                if command in (lint.command(prepare=True), lint.command(['Fixture'])):
                    result = subprocess.run(command, cwd=self.root, env=self.environment,
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=90)
                    if command == lint.command(['Fixture']):
                        owner.assertIn('using original full lintCore', result.stdout)
                    if result.returncode:
                        self.calls.append(command)
                        raise CommandFailed(result.stdout, result.returncode)
                return super().run(task, directory)

        runtime = LintRuntime(self.root)
        runtime.environment = self.env
        auditor = self.root / '.lake/axiom-audit/.lake/build/bin/axiom-audit'
        auditor.parent.mkdir(parents=True)
        auditor.write_bytes(b'fixed synthetic auditor; unrelated to native lint')
        with patch('lean_tools.local._prepare_auditor', return_value=auditor):
            first = local.check(self.root, ['Fixture'], runtime=runtime)
            self.assertIn('lint', first['performed_checks'])
            # No Lean source, configuration or compiled input changes here.
            external.write_text('fail')
            with self.assertRaisesRegex(ValueError, 'external linter failure'):
                local.check(self.root, ['Fixture'], runtime=runtime)
        self.assertEqual(runtime.calls.count(lint.command(['Fixture'])), 2)
        from lean_tools.state import read_json
        records = (self.root / '.lake/native-checks/progress').glob('*.json')
        self.assertNotIn('lint', [read_json(path)['binding']['kind'] for path in records])

    def test_global_auto_declaration_change_is_checked_again(self):
        self.append("Fixture/Left.lean", '\nnamespace N\n'
            'public theorem «mutual» : 0 = 0 := rfl\nend N\n')
        self.append("Fixture/Right.lean", '\nnamespace N\n'
            'public inductive _functor : Prop where\n  | mk\nend N\n')
        self.native()
        self.batched()
        right = self.root / "Fixture/Right.lean"
        right.write_text(right.read_text().split('\nnamespace N\n')[0])
        self.build()
        self.native(1)
        self.batched(1)

    def test_arbitrary_scope_multi_root_and_custom_full_api(self):
        config = self.root / "lakefile.toml"
        config.write_text(config.read_text().replace('["--no-build", "Fixture"]',
            '["--no-build", "Fixture.Left", "Fixture.Right"]'))
        self.build()
        self.native(roots=("Fixture.Right",))
        output = self.batched(roots=("Fixture.Right",))
        self.assertIn("[Fixture.Left] importing full lint environment (persistent=false)", output)
        self.assertIn("[Fixture.Right] importing full lint environment (persistent=false)", output)
        self.append("Fixture/Left.lean", '\nopen Lean\n'
            '@[env_linter] public meta def customCheck : Batteries.Tactic.Lint.Linter where\n'
            '  noErrorsFound := "ok"\n  errorsFound := "failed"\n'
            '  test decl := do\n    if decl == `Fixture.leftValue then return m!"custom failure"\n'
            '    return none\n')
        self.native(1, roots=("Fixture.Right",))
        output = self.batched(1, roots=("Fixture.Right",))
        self.assertIn("using original full lintCore", output)
        self.assertIn("custom failure", output)

    def test_builtin_disabled_or_absent_retains_native_fallback(self):
        path = self.root / "lakefile.toml"
        original = path.read_text()
        for replacement in ('builtinLint = false\n', ''):
            path.write_text(original.replace('builtinLint = true\n', replacement))
            self.build()
            self.assertFalse(preflight.supported(self.root))
            self.native(1)
            output = self.batched(1)
            self.assertNotIn("full lint:", output)

    def test_driver_still_executes_after_builtin_findings(self):
        self.append("Fixture/Left.lean", '\nnamespace Fixture\n'
            'set_option linter.unusedVariables true\n'
            '/-- A declaration with a syntax-only warning. -/\n'
            '@[nolint unusedArguments] public def syntaxWarning (unused : Nat) : Nat := 0\n'
            'end Fixture\n')
        self.native(1)
        output = self.batched(1)
        self.assertIn("builtin exit=1", output)
        self.assertIn("Completed linting!", output)
        self.assertIn("-- Linting passed for Fixture.", output)

    def test_active_lean_configuration_precedes_supported_toml(self):
        (self.root / "lakefile.lean").write_text(
            'import Lake\nopen Lake DSL\npackage Fixture where\n'
            '  lintDriver := "activeLint"\n  builtinLint := true\n'
            'require batteries from ' + json.dumps(str(self.batteries)) + '\n'
            'lean_lib Fixture\nscript activeLint (_args) do\n'
            '  IO.println "active Lean driver failed"\n  return 7\n')
        self.assertFalse(preflight.supported(self.root))
        native = self.native(7)
        output = self.batched(7)
        self.assertIn("active Lean driver failed", native)
        self.assertIn("active Lean driver failed", output)
        self.assertNotIn("backend=batched", output)
        self.assertFalse((self.root / ".lake/lint-runner").exists())

    def test_redirected_provider_configuration_falls_back_before_preparation(self):
        directory = self.root / "redirected-provider"
        for name in preflight.SOURCES:
            target = directory / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(self.batteries / name, target)
        manifest_path = self.root / "lake-manifest.json"
        manifest = json.loads(manifest_path.read_text())
        package, = [p for p in manifest["packages"] if p["name"] == "batteries"]
        package["dir"] = str(directory)
        manifest_path.write_text(json.dumps(manifest))
        self.assertTrue(preflight.supported(self.root))
        binary = self.root / "fake-bin"
        binary.mkdir()
        fake = binary / "lake"
        fake.write_text('#!/usr/bin/env python3\nimport json,os,sys\n'
            'print(json.dumps({"args":sys.argv[1:],"threads":os.environ.get("LEAN_NUM_THREADS")}))\n')
        fake.chmod(0o755)
        environment = {"PATH": str(binary) + os.pathsep + self.env["PATH"], "CI_LINT_WORKERS": "4"}

        def rejected():
            self.assertFalse(preflight.supported(self.root))
            output = self.command(["bash", str(HELPER / "run.sh"), "Fixture"], extra_env=environment)
            record = json.loads(output)
            self.assertEqual(record["threads"], "1")
            self.assertEqual(record["args"], ["--no-build", "lint", "Fixture", "--", "--trace"])
            self.assertFalse((self.root / ".lake/lint-runner").exists())

        config = directory / "lakefile.toml"
        original = config.read_text()
        config.write_text(original.replace('srcDir = "scripts"', 'srcDir = "redirected"\nroot = "OtherRunner"'))
        rejected()
        config.write_text(original)
        for key, value in (("configFile", "redirected.toml"), ("manifestFile", "other.json"),
                           ("subDir", "redirected")):
            before = package.get(key)
            package[key] = value
            manifest_path.write_text(json.dumps(manifest))
            rejected()
            if before is None:
                package.pop(key)
            else:
                package[key] = before
            manifest_path.write_text(json.dumps(manifest))
        (directory / "lakefile.lean").write_text("active provider configuration")
        rejected()

    def test_restored_private_lean_config_cannot_redirect_helper(self):
        self.append("Fixture/Left.lean", '\nnamespace Fixture\n'
            'public theorem localTaut : True = True := rfl\nend Fixture\n')
        tool = self.root / ".lake/lint-runner"
        tool.mkdir(parents=True)
        (tool / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
        (tool / "lakefile.lean").write_text('import Lake\nopen Lake DSL\n'
            'package Poison\nlean_exe batchedLint where\n  root := `Poison\n')
        (tool / "Poison.lean").write_text('def main : IO Unit := IO.println "POISON-HELPER"\n')
        self.command([self.lake, "--dir", str(tool), "build", "batchedLint"])
        self.native(1)
        output = self.batched(1)
        self.assertIn("backend=batched", output)
        self.assertIn("LHS equals RHS syntactically", output)
        self.assertNotIn("POISON-HELPER", output)

    def test_private_tool_manifest_resolves_current_provider(self):
        self.batched()
        original_manifest = (self.root / "lake-manifest.json").read_bytes()
        private = self.root / ".lake/lint-runner/lake-manifest.json"
        manifest = json.loads(private.read_text())
        manifest["packages"][0]["dir"] = str(self.root / "nonexistent-old-provider")
        private.write_text(json.dumps(manifest))
        output = self.batched()
        self.assertIn("backend=batched", output)
        actual = json.loads(private.read_text())["packages"][0]
        self.assertEqual(Path(actual["dir"]).resolve(), self.batteries)
        self.assertEqual((self.root / "lake-manifest.json").read_bytes(), original_manifest)
        self.assertEqual((self.root / ".lake/lint-runner/lean-toolchain").read_text(),
                         "leanprover/lean4:v4.34.1\n")

    def test_root_package_overrides_retains_native_fallback_and_threads(self):
        overrides = self.root / ".lake/package-overrides.json"
        overrides.write_text("[]\n")
        self.assertFalse(preflight.supported(self.root))
        binary = self.root / "fake-bin"
        binary.mkdir()
        fake = binary / "lake"
        fake.write_text('#!/usr/bin/env python3\nimport json,os,sys\n'
            'print(json.dumps({"args":sys.argv[1:],"threads":os.environ.get("LEAN_NUM_THREADS")}))\n')
        fake.chmod(0o755)
        output = self.command(["bash", str(HELPER / "run.sh"), "Fixture"], extra_env={
            "PATH": str(binary) + os.pathsep + self.env["PATH"], "CI_LINT_WORKERS": "4"})
        record = json.loads(output)
        self.assertEqual(record["args"], ["--no-build", "lint", "Fixture", "--", "--trace"])
        self.assertEqual(record["threads"], "1")
        self.assertEqual(overrides.read_text(), "[]\n")
        self.assertFalse((self.root / ".lake/lint-runner").exists())

    def test_custom_package_directories_retain_native_fallback(self):
        binary = self.root / "fake-bin"
        binary.mkdir()
        fake = binary / "lake"
        fake.write_text('#!/usr/bin/env python3\nimport json,os,sys\n'
            'print(json.dumps({"args":sys.argv[1:],"threads":os.environ.get("LEAN_NUM_THREADS")}))\n')
        fake.chmod(0o755)
        environment = {"PATH": str(binary) + os.pathsep + self.env["PATH"], "CI_LINT_WORKERS": "4"}
        config = self.root / "lakefile.toml"
        original = config.read_text()
        manifest = self.root / "lake-manifest.json"
        for owner in ("config", "manifest"):
            if owner == "config":
                config.write_text('packagesDir = ".lake/other"\n' + original)
            else:
                config.write_text(original)
                value = json.loads(manifest.read_text())
                value["packagesDir"] = ".lake/other"
                manifest.write_text(json.dumps(value))
            self.assertFalse(preflight.supported(self.root))
            output = self.command(["bash", str(HELPER / "run.sh"), "Fixture"], extra_env=environment)
            record = json.loads(output)
            self.assertEqual(record["args"], ["--no-build", "lint", "Fixture", "--", "--trace"])
            self.assertEqual(record["threads"], "1")
            self.assertFalse((self.root / ".lake/lint-runner").exists())

    def test_batch_backend_state_budgets_interrupts_and_worker_failures(self):
        compiled = self.root / "probe-modules"
        compiled.mkdir()
        shutil.copyfile(HELPER / "BatchedLint.lean", compiled / "BatchedLint.lean")
        self.command([self.lake, "env", "lean", "-o", str(compiled / "BatchedLint.olean"),
            str(compiled / "BatchedLint.lean")])
        sysroot = Path(self.command([self.lake, "env", "lean", "--print-prefix"]).strip())
        library = sysroot / "lib/lean/libLake_shared.so"
        if not library.exists():
            library = library.with_suffix(".dylib")
        output = self.command([self.lake, "env", "lean", "--load-dynlib", str(library),
            str(FIXTURES / "PoolProbe.lean")], extra_env={"LEAN_PATH": str(compiled)})
        self.assertIn("pool-probe:", output)

    def test_worker_environment_and_unsupported_version_fallback(self):
        binary = self.root / "fake-bin"
        binary.mkdir()
        fake = binary / "lake"
        source = ('#!/usr/bin/env python3\nimport json,os,sys\n'
            'if sys.argv[1:] == ["env","lean","--version"]:\n'
            ' print(os.environ.get("TEST_LEAN_VERSION", "Lean (version 4.34.1, fixture)"))\n'
            'else:\n'
            ' print(json.dumps({"args":sys.argv[1:],"threads":os.environ.get("LEAN_NUM_THREADS")}))\n')
        fake.write_text(source)
        fake.chmod(0o755)
        env = {"PATH": str(binary) + os.pathsep + self.env["PATH"], "CI_LINT_WORKERS": "4"}
        output = self.command(["bash", str(HELPER / "run.sh"), "Fixture"], extra_env=env)
        record = json.loads(output.splitlines()[-1])
        available = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else (os.cpu_count() or 1)
        self.assertEqual(record["threads"], str(min(4, available)))
        self.assertEqual(record["args"][0], "env")
        self.assertTrue(record["args"][1].endswith("/batchedLint"))
        env["LEAN_TOOLS_LINT_MAX_THREADS"] = "1"
        output = self.command(["bash", str(HELPER / "run.sh"), "Fixture"], extra_env=env)
        self.assertEqual(json.loads(output.splitlines()[-1])["threads"], "1")
        env["TEST_LEAN_VERSION"] = "Lean (version 4.35.0, fixture)"
        output = self.command(["bash", str(HELPER / "run.sh"), "Fixture"], extra_env=env)
        record = json.loads(output)
        self.assertEqual(record["threads"], "1")
        self.assertEqual(record["args"], ["--no-build", "lint", "Fixture", "--", "--trace"])


if __name__ == "__main__":
    unittest.main()
