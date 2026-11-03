"""Exercise native workflow failure gates without running Lean (requires PyYAML)."""
import os
import io
import hashlib
import json
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time
import tomllib
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = yaml.safe_load((ROOT / '.github/workflows/lean-ci.yml').read_text())
JOBS = WORKFLOW['jobs']


def step(job, name):
    return next(item for item in JOBS[job]['steps'] if item.get('name') == name)



def runner_arguments(command):
    """Model ProcessStartInfo.Arguments on Unix, as used by actions/runner.

    Based on dotnet/runtime v8.0.12 Process.Unix.cs GetNextArgument;
    single quotes are literal, and only double quotes group an argument.
    """
    result, index = [], 0
    while index < len(command):
        if command[index] in ' \t':
            index += 1
            continue
        argument, quoted = '', False
        while index < len(command):
            count = 0
            while index < len(command) and command[index] == '\\':
                count += 1
                index += 1
            if count:
                if index == len(command) or command[index] != '"':
                    argument += '\\' * count
                else:
                    argument += '\\' * (count // 2)
                    if count % 2:
                        argument += '"'
                        index += 1
                continue
            char = command[index]
            if char == '"':
                if quoted and command[index:index + 2] == '""':
                    argument += '"'
                    index += 1
                else:
                    quoted = not quoted
            elif char in ' \t' and not quoted:
                break
            else:
                argument += char
            index += 1
        result.append(argument)
    return result


def condition(expression, values, *, success=True, cancelled=False):
    """Evaluate this workflow's conditions, including implicit success()."""
    values = {'inputs.first-ci-cache': '', 'steps.cache-mode.outputs.layered': '', **values}
    text = expression.removeprefix('${{').removesuffix('}}').strip()
    explicit_status = re.search(r'\b(always|cancelled|success|failure)\(', text)
    if not explicit_status and not success:
        return False
    text = re.sub(r'\b(?:needs|steps|github|inputs)(?:\.[\w-]+)+',
                  lambda match: repr(values[match[0]]), text)
    text = text.replace('always()', 'True').replace('cancelled()', repr(cancelled))
    text = text.replace('&&', ' and ').replace('||', ' or ')
    text = re.sub(r'!(?!=)', ' not ', text)
    return bool(eval(text, {'__builtins__': {}, 'format': str.format}, {}))


def report(name, outcomes):
    with tempfile.TemporaryDirectory(prefix='lean-ci-report-') as directory:
        return subprocess.run(
            ['bash', '-e', '-o', 'pipefail', '-c', step(*name)['run']],
            env={**os.environ, **outcomes, 'GITHUB_STEP_SUMMARY': directory + '/summary'},
            capture_output=True, text=True, check=False).returncode


def publish(build='success', tests='success', staged='true', event='push', ref='refs/heads/main'):
    return condition(JOBS['upload_cache']['if'], {
        'needs.build.result': build, 'needs.test_lint.result': tests,
        'needs.build.outputs.staged': staged,
        # Misleading successful outputs must never override a failed job.
        'needs.build.outputs.outcome': 'success',
        'github.event_name': event, 'github.ref': ref,
        'github.event.repository.default_branch': 'main',
    })


class WorkflowGates(unittest.TestCase):
    def test_final_reports_cannot_mask_failed_or_skipped_checks(self):
        for job, name in (('build', 'Report Build result'),
                          ('test_lint', 'Report Test, lint and axiom results')):
            final = step(job, name)
            self.assertFalse(final.get('continue-on-error', False))
            self.assertFalse(JOBS[job].get('continue-on-error', False))
            self.assertTrue(condition(final['if'], {}, success=False, cancelled=True))

    def test_build_report_requires_only_the_mathematical_build(self):
        self.assertEqual(step('build', 'Report Build result')['env'],
                         {'RESULT': '${{ steps.build.outcome }}'})
        self.assertEqual(report(('build', 'Report Build result'),
                                {'RESULT': 'success', 'TOOLS': 'failure',
                                 'IMPORTS': 'failure', 'STYLE': 'failure', 'AXIOMS': 'failure'}), 0)
        for outcome in ('failure', 'skipped', 'cancelled'):
            self.assertNotEqual(report(('build', 'Report Build result'), {'RESULT': outcome}), 0)
            self.assertFalse(publish(build='failure'))

    def test_setup_or_build_failure_prevents_downstream_job(self):
        # Setup failure skips Build, whose report then fails. Test must never
        # start against partial production output.
        for result in ('success', 'failure', 'skipped', 'cancelled'):
            with self.subTest(result=result):
                allowed = condition(JOBS['test_lint']['if'], {'needs.build.result': result})
                self.assertEqual(allowed, result == 'success')

    def test_feedback_survives_test_failure_but_requires_its_prerequisites(self):
        for name in ('Lint', 'Audit production axioms'):
            success = {'needs.build.result': 'success',
                       'steps.lean-setup.outcome': 'success', 'steps.compiled.outcome': 'success',
                       'steps.tools.outcome': 'success'}
            self.assertTrue(condition(step('test_lint', name)['if'], success, success=False))
            self.assertFalse(condition(step('test_lint', name)['if'], success,
                                       success=False, cancelled=True))
            for key in success:
                for outcome in ('failure', 'skipped', 'cancelled'):
                    with self.subTest(step=name, prerequisite=key, outcome=outcome):
                        allowed = condition(step('test_lint', name)['if'],
                                            {**success, key: outcome}, success=False)
                        # The auditor prepares its own tool, independently of
                        # the declaration/style/helper tool build.
                        self.assertEqual(allowed,
                                         name == 'Audit production axioms' and key == 'steps.tools.outcome')

    def test_each_check_failure_or_skip_fails_report_and_blocks_publication(self):
        success = dict.fromkeys(('COMPILED', 'TOOLS', 'IMPORTS', 'STYLE', 'TEST', 'LINT', 'AXIOMS'), 'success')
        self.assertEqual(report(('test_lint', 'Report Test, lint and axiom results'), success), 0)
        for check in success:
            for outcome in ('failure', 'skipped', 'cancelled'):
                with self.subTest(check=check, outcome=outcome):
                    result = report(('test_lint', 'Report Test, lint and axiom results'),
                                    {**success, check: outcome})
                    self.assertNotEqual(result, 0)
                    self.assertFalse(publish(tests='failure'))

    def test_publication_requires_both_jobs_even_with_staged_success_outputs(self):
        self.assertEqual(set(JOBS['upload_cache']['needs']), {'build', 'test_lint'})
        for job in ('build', 'tests'):
            for outcome in ('failure', 'skipped', 'cancelled'):
                with self.subTest(job=job, outcome=outcome):
                    self.assertFalse(publish(**{job: outcome}))
        self.assertTrue(publish())

    def test_publication_is_only_a_staged_trusted_default_branch_push(self):
        for values in ({'staged': 'false'}, {'staged': ''}, {'event': 'pull_request'},
                       {'event': 'workflow_dispatch'}, {'ref': 'refs/heads/topic'},
                       {'ref': 'refs/pull/1/merge'}):
            with self.subTest(values=values):
                self.assertFalse(publish(**values))

    def test_failure_and_cancellation_keep_cache_cleanup_enabled(self):
        for job, name in (('build', 'Save compilation independently of Test and lint'),
                          ('test_lint', 'Save completed Test compilation')):
            values = {'steps.quiesce.outcome': 'success'}
            self.assertTrue(condition(step(job, name)['if'], values, success=False))
            self.assertTrue(condition(step(job, name)['if'], values, success=False, cancelled=True))

    def test_legacy_path_restores_native_and_lake_cache_once_together(self):
        for name in ('build', 'test_lint'):
            restores = [item for item in JOBS[name]['steps']
                        if item.get('uses', '').startswith('actions/cache/restore@')]
            broad = [item for item in restores if '/.lake' in item['with']['path']]
            self.assertEqual(len(broad), 1, name)
            paths = broad[0]['with']['path'].splitlines()
            self.assertEqual(paths, ['${{ inputs.package-directory }}/.lake',
                                     '${{ runner.temp }}/lake-native-cache'])
        self.assertNotIn('native-key', [item.get('id') for item in JOBS['build']['steps']])

    def test_cache_fallback_reuses_changed_pins_and_existing_key_generations(self):
        restore = next(item for item in JOBS['build']['steps'] if item.get('id') == 'restore')['with']
        values = {'runner.os': 'Linux', 'runner.arch': 'X64', 'github.sha': 'commit',
                  'github.run_id': 'run', 'github.run_attempt': '1',
                  'inputs.first-ci-cache': '', 'steps.first-ci.outputs.seed-key': 'seed',
                  "hashFiles(format('{0}/lean-toolchain', inputs.package-directory))": 'compiler',
                  "hashFiles(format('{0}/lake-manifest.json', inputs.package-directory))": 'pins',
                  "hashFiles(format('{0}/lean-toolchain', inputs.package-directory), "
                  "format('{0}/lake-manifest.json', inputs.package-directory))": 'legacy-pins'}

        def render(text):
            def evaluate(match):
                expression = match[1]
                for key in sorted((key for key in values if key.startswith('hashFiles(')),
                                  key=len, reverse=True):
                    expression = expression.replace(key, repr(values[key]))
                expression = re.sub(r'\b(?:runner|github|inputs|steps)(?:\.[\w-]+)+',
                                    lambda token: repr(values[token[0]]), expression)
                expression = expression.replace('&&', ' and ').replace('||', ' or ')
                return str(eval(expression, {'__builtins__': {}, 'format': str.format}, {}))
            return re.sub(r'\$\{\{\s*(.*?)\s*\}\}', evaluate, text)

        primary = render(restore['key'])
        prefixes = render(restore['restore-keys']).splitlines()
        self.assertEqual(primary, 'lean-Linux-X64-compiler-pins-commit-run-1')
        # Keys are newest-first; the action still tries each restore prefix in order.
        candidates = ['lean-Linux-X64-other-compiler-other-pins-newest',
                      'lean-Linux-X64-legacy-other-pins-previous',
                      'lean-Linux-X64-legacy-pins-previous',
                      'lean-Linux-X64-compiler-old-pins-previous',
                      'lean-Linux-X64-compiler-pins-previous']
        for remaining, expected in ((candidates, candidates[-1]),
                                    (candidates[:-1], candidates[-2]),
                                    (candidates[:-2], candidates[-3]),
                                    (candidates[:2], candidates[0])):
            with self.subTest(expected=expected):
                selected = next((key for prefix in prefixes for key in remaining
                                 if key.startswith(prefix)), None)
                self.assertEqual(selected, expected)
        for key in ('lean-Windows-X64-compiler-pins-old', 'lean-Linux-ARM64-compiler-pins-old'):
            self.assertFalse(any(key.startswith(prefix) for prefix in prefixes))
        self.assertIn('lake build --rehash "${targets[@]}"', step('build', 'Build')['run'])

    def test_native_checks_and_full_text_style_are_preserved(self):
        self.assertIn('mathlib/mk_all --lib "$root" --check',
                      step('test_lint', 'Check generated library entries')['run'])
        self.assertIn('lake --no-build exe mathlib/lint-style "${roots[@]}"',
                      step('test_lint', 'Mathlib text style')['run'])
        self.assertIn('lake --no-build lint "${roots[@]}" -- --trace',
                      step('test_lint', 'Lint')['run'])
        self.assertEqual(step('test_lint', 'Test')['run'], 'lake test')
        self.assertIn('--root "$root"', step('test_lint', 'Audit production axioms')['run'])


class RestoredArchiveHashMetadata(unittest.TestCase):
    name = 'Remove read-only restored archive hash sidecars'

    def cleanup(self, root):
        return subprocess.run(['bash', '-e', '-o', 'pipefail', '-c',
                               step('build', self.name)['run']], cwd=root,
                              capture_output=True, text=True)

    def test_both_jobs_clean_restored_metadata_before_first_lake_invocation(self):
        for job in ('build', 'test_lint'):
            actions = JOBS[job]['steps']
            cleanup = step(job, self.name)
            restore = next(item for item in actions
                           if item.get('uses', '').startswith('actions/cache/restore@'))
            self.assertEqual(cleanup['run'], step('build', self.name)['run'])
            self.assertEqual(cleanup['working-directory'], '${{ inputs.package-directory }}')
            self.assertLess(actions.index(restore), actions.index(cleanup))
            self.assertLess(actions.index(cleanup), actions.index(step(job, 'Configure Lean')))
        self.assertIn('lake build --rehash', step('build', 'Build')['run'])

    def test_tar_restored_readonly_sidecar_is_regenerated_without_mutating_artifacts(self):
        with tempfile.TemporaryDirectory(prefix='restored-archive-hash-') as directory:
            root = Path(directory)
            source = root / 'source'
            ir = source / '.lake/build/ir/Aglib/Path with spaces'
            ir.mkdir(parents=True)
            cached = source / 'native-cache/artifacts/immutable'
            cached.parent.mkdir(parents=True)
            cached.write_text('0123456789abcdef')
            readonly = ir / 'ToUnit.ltar.hash'
            os.link(cached, readonly)
            cached.chmod(0o444)
            for name, content, mode in (('Writable.ltar.hash', 'keep writable hash', 0o644),
                                         ('ToUnit.ltar', 'immutable archive', 0o444),
                                         ('ToUnit.olean.hash', 'other hash metadata', 0o444)):
                path = ir / name
                path.write_text(content)
                path.chmod(mode)
            archive = root / 'cache.tar'
            with tarfile.open(archive, 'w') as stream:
                stream.add(source / '.lake', arcname='.lake')
                stream.add(source / 'native-cache', arcname='native-cache')
            restored = root / 'restored'
            restored.mkdir()
            subprocess.run(['tar', '-xf', str(archive), '-C', str(restored)], check=True)
            ir = restored / ir.relative_to(source)
            cached = restored / cached.relative_to(source)
            readonly = ir / readonly.name
            self.assertEqual(readonly.stat().st_ino, cached.stat().st_ino)
            self.assertEqual(readonly.stat().st_mode & 0o777, 0o444)
            external = root / 'external'
            external.mkdir()
            target = external / 'Outside.ltar.hash'
            target.write_text('external metadata')
            target.chmod(0o444)
            (ir / 'Linked.ltar.hash').symlink_to(target)
            (ir / 'linked-directory').symlink_to(external, target_is_directory=True)
            result = self.cleanup(restored)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('Removed 1 read-only', result.stdout)
            self.assertFalse(readonly.exists())
            readonly.write_text('fedcba9876543210')  # Native rehash can recreate the sidecar.
            self.assertTrue(readonly.stat().st_mode & 0o200)
            self.assertEqual(cached.read_text(), '0123456789abcdef')
            self.assertEqual(cached.stat().st_mode & 0o777, 0o444)
            self.assertEqual((ir / 'ToUnit.ltar').read_text(), 'immutable archive')
            self.assertEqual((ir / 'ToUnit.ltar').stat().st_mode & 0o777, 0o444)
            self.assertEqual((ir / 'Writable.ltar.hash').read_text(), 'keep writable hash')
            self.assertEqual((ir / 'ToUnit.olean.hash').read_text(), 'other hash metadata')
            self.assertTrue((ir / 'Linked.ltar.hash').is_symlink())
            self.assertEqual(target.read_text(), 'external metadata')
            self.assertEqual(target.stat().st_mode & 0o777, 0o444)

    def test_missing_build_tree_is_a_noop(self):
        with tempfile.TemporaryDirectory(prefix='missing-archive-hash-') as root:
            self.assertEqual(self.cleanup(root).returncode, 0)
            self.assertEqual(list(Path(root).iterdir()), [])

    def test_late_restoration_is_cleaned_after_all_cache_preparation(self):
        for job, consumer in (('build', 'Build'),
                              ('test_lint', 'Verify Build outputs without compilation')):
            actions = JOBS[job]['steps']
            cleanup = step(job, 'Refresh archive hash metadata after cache preparation')
            self.assertEqual(cleanup['run'], step(job, self.name)['run'])
            self.assertEqual(cleanup['working-directory'], '${{ inputs.package-directory }}')
            self.assertEqual(actions[actions.index(cleanup) + 1]['name'], consumer)
            preparation = ('Restore published native dependency caches' if job == 'build'
                           else "Restore this run's native Build outputs")
            self.assertLess(actions.index(step(job, preparation)), actions.index(cleanup))
        with tempfile.TemporaryDirectory(prefix='late-archive-hash-') as directory:
            self.assertEqual(self.cleanup(directory).returncode, 0)
            ir = Path(directory) / '.lake/build/ir/Aglib'
            ir.mkdir(parents=True)
            late = ir / 'AssociatedBundle.ltar.hash'
            late.write_text('0123456789abcdef')
            late.chmod(0o444)
            self.assertEqual(self.cleanup(directory).returncode, 0)
            self.assertFalse(late.exists())

    def test_pinned_lake_replay_packs_missing_archive_and_repairs_only_hash_metadata(self):
        # A software fixture only: no Aglib, Mathlib, dependency or project proofs.
        toolchain = (ROOT / 'lean-toolchain').read_text().strip()
        toolchain_name = toolchain.replace('/', '--').replace(':', '---')
        lake = Path(os.environ.get('ELAN_HOME', Path.home() / '.elan')) / 'toolchains' / toolchain_name / 'bin/lake'
        if not lake.is_file():
            self.skipTest('pinned native Lake is not installed; do not download a toolchain')
        with tempfile.TemporaryDirectory(prefix='native-replay-hash-') as directory:
            root = Path(directory)
            (root / 'lean-toolchain').write_text(toolchain + '\n')
            (root / 'lakefile.toml').write_text(
                'name = "fixture"\nenableArtifactCache = true\nrestoreAllArtifacts = true\n'
                '[[lean_lib]]\nname = "Fixture"\n')
            (root / 'Fixture.lean').write_text('def fixtureValue : Nat := 1\n')
            cache = root / 'native-cache'
            env = {**os.environ, 'LAKE_ARTIFACT_CACHE': 'true', 'LAKE_CACHE_DIR': str(cache)}
            command = [str(lake), 'build', '--rehash', 'Fixture', '-o', 'outputs.jsonl']
            def build():
                return subprocess.run(command, cwd=root, env=env, capture_output=True,
                                      text=True, timeout=30)
            first = build()
            self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
            olean = root / '.lake/build/lib/lean/Fixture.olean'
            original = (olean.read_bytes(), olean.stat().st_ino, olean.stat().st_mtime_ns)
            mappings = {p.relative_to(cache): p.read_bytes()
                        for p in (cache / 'outputs').rglob('*') if p.is_file()}
            self.assertEqual(self.cleanup(root).returncode, 0)
            archive = root / '.lake/build/ir/Fixture.ltar'
            sidecar = archive.with_suffix('.ltar.hash')
            archive.unlink()
            sidecar.chmod(0o444)  # Simulates read-only metadata restored after startup.
            failed = build()
            self.assertNotEqual(failed.returncode, 0)
            failure_log = failed.stdout + failed.stderr
            self.assertIn('Replaying Fixture', failure_log)
            self.assertIn('leantar -s', failure_log)
            self.assertIn('failed to cache artifact: permission denied', failure_log)
            self.assertIn('Fixture.ltar.hash', failure_log)
            self.assertEqual(self.cleanup(root).returncode, 0)
            repaired = build()
            self.assertEqual(repaired.returncode, 0, repaired.stdout + repaired.stderr)
            self.assertEqual((olean.read_bytes(), olean.stat().st_ino, olean.stat().st_mtime_ns), original)
            self.assertEqual({p.relative_to(cache): p.read_bytes()
                              for p in (cache / 'outputs').rglob('*') if p.is_file()}, mappings)
            self.assertNotIn('Built Fixture', repaired.stdout + repaired.stderr)

    def test_symlink_ancestors_and_nonwritable_directories_fail_before_unlink(self):
        for ancestor in ('.lake', '.lake/build', '.lake/build/ir'):
            with self.subTest(ancestor=ancestor), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                external = root / 'external'
                external.mkdir()
                path = root / ancestor
                path.parent.mkdir(parents=True, exist_ok=True)
                path.symlink_to(external, target_is_directory=True)
                result = self.cleanup(root)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('Unsafe restored build directory', result.stderr)
                self.assertEqual(list(external.iterdir()), [])
        with tempfile.TemporaryDirectory() as directory:
            ir = Path(directory) / '.lake/build/ir/Aglib'
            ir.mkdir(parents=True)
            sidecar = ir / 'ToUnit.ltar.hash'
            sidecar.write_text('0123456789abcdef')
            sidecar.chmod(0o444)
            ir.chmod(0o555)
            try:
                result = self.cleanup(directory)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('Unsafe restored build directory', result.stderr)
                self.assertTrue(sidecar.exists())
            finally:
                ir.chmod(0o755)


class BuildJobBudget(unittest.TestCase):
    def test_deadline_is_first_and_includes_setup_time(self):
        first = JOBS['build']['steps'][0]
        self.assertEqual(first['name'], 'Set Build deadline')
        self.assertEqual(first['shell'], 'bash')
        self.assertEqual(first['env']['JOB_TIMEOUT_MINUTES'], '${{ inputs.job-timeout-minutes }}')
        for minutes, budget in ((360, 330), (150, 120), (90, 60), (31, 1)):
            with self.subTest(minutes=minutes), tempfile.TemporaryDirectory(prefix='lean-ci-deadline-') as directory:
                environment_file = Path(directory) / 'github-env'
                result = subprocess.run(
                    ['bash', '-e', '-o', 'pipefail', '-c',
                     'date() { printf "1000\\n"; }\n' + first['run']],
                    env={**os.environ, 'GITHUB_ENV': str(environment_file), 'JOB_TIMEOUT_MINUTES': str(minutes)},
                    capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                exported = dict(line.split('=', 1) for line in environment_file.read_text().splitlines())
                deadline = int(exported['BUILD_DEADLINE'])
                self.assertEqual(deadline - 1000, budget * 60)
                self.assertEqual(int(exported['BUILD_COMPILER_MINUTES']), budget)
                result, calls, partial = self.run_build(deadline=deadline, now=1000, compiler_minutes=budget)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(calls, [
                    f'timeout:--signal=INT --kill-after=60s {budget * 60}s lake build --rehash Aglib Quillen -o ./outputs.jsonl',
                    'lake:build --rehash Aglib Quillen -o ./outputs.jsonl'])
                self.assertTrue(partial)
                result, calls, partial = self.run_build(deadline=deadline, now=deadline, compiler_minutes=budget)
                self.assertEqual(result.returncode, 124)
                self.assertIn(f'{budget}-minute compiler budget', result.stdout)
                self.assertEqual(calls, [])

    def test_invalid_job_timeout_fails_before_exporting_deadline(self):
        for value in ('', '0', '30', '-1', '150.5', 'invalid'):
            with self.subTest(value=value), tempfile.TemporaryDirectory(prefix='lean-ci-deadline-') as directory:
                environment_file = Path(directory) / 'github-env'
                result = subprocess.run(['bash', '-eo', 'pipefail', '-c', step('build', 'Set Build deadline')['run']],
                    env={**os.environ, 'GITHUB_ENV': str(environment_file), 'JOB_TIMEOUT_MINUTES': value},
                    capture_output=True, text=True)
                self.assertEqual(result.returncode, 2)
                self.assertIn('greater than 30', result.stderr)
                self.assertFalse(environment_file.exists())

    def run_build(self, *, deadline=20800, now=1000, compiler_status=0, timeout_status=0, compiler_minutes=330):
        mock = r'''
date() { printf '%s\n' "$FIXTURE_NOW"; }
lake() {
  printf 'lake:%s\n' "$*" >> "$TRACE"
  echo completed-module > "$PARTIAL"
  return "$COMPILER_STATUS"
}
timeout() {
  printf 'timeout:%s\n' "$*" >> "$TRACE"
  shift 3
  if test "$TIMEOUT_STATUS" -ne 0; then
    "$@" || return "$?"
    return "$TIMEOUT_STATUS"
  fi
  "$@"
}
'''
        with tempfile.TemporaryDirectory(prefix='lean-ci-build-budget-') as directory:
            root = Path(directory)
            trace = root / 'trace'
            result = subprocess.run(
                ['bash', '-e', '-o', 'pipefail', '-c', mock + step('build', 'Build')['run']],
                cwd=root, env={**os.environ, 'BUILD_TARGETS': 'Aglib Quillen',
                               'BUILD_DEADLINE': str(deadline), 'FIXTURE_NOW': str(now),
                               'BUILD_COMPILER_MINUTES': str(compiler_minutes),
                               'RUNNER_TEMP': '.', 'TRACE': str(trace), 'PARTIAL': str(root / 'completed'),
                               'COMPILER_STATUS': str(compiler_status), 'TIMEOUT_STATUS': str(timeout_status)},
                capture_output=True, text=True)
            return result, trace.read_text().splitlines() if trace.exists() else [], (root / 'completed').exists()

    def test_expired_budget_never_invokes_lake_or_timeout(self):
        for now in (20800, 20801):
            with self.subTest(now=now):
                result, calls, partial = self.run_build(now=now)
                self.assertEqual(result.returncode, 124)
                self.assertEqual(calls, [])
                self.assertFalse(partial)
                self.assertIn('330-minute compiler budget', result.stdout)
                self.assertIn('rerun this branch', result.stdout)
                self.assert_failed_build_blocks_consumers(result.returncode)

    def test_success_and_compile_errors_are_unchanged_without_retry(self):
        for status in (0, 1, 2):
            with self.subTest(status=status):
                result, calls, partial = self.run_build(compiler_status=status)
                self.assertEqual(result.returncode, status, result.stderr)
                self.assertEqual(sum(call.startswith('lake:') for call in calls), 1)
                self.assertTrue(partial)
                self.assertNotIn('::warning::', result.stdout)

    def test_timeout_and_forced_kill_fail_after_preserving_completed_outputs(self):
        for status in (124, 137):
            with self.subTest(status=status):
                result, calls, partial = self.run_build(timeout_status=status)
                self.assertEqual(result.returncode, status, result.stderr)
                self.assertEqual(sum(call.startswith('lake:') for call in calls), 1)
                self.assertTrue(partial)
                self.assertIn(f'timeout/kill status {status}', result.stdout)
                self.assertIn('rerun this branch', result.stdout)
                self.assert_failed_build_blocks_consumers(result.returncode)

    def assert_failed_build_blocks_consumers(self, status):
        self.assertNotEqual(status, 0)
        self.assertTrue(step('build', 'Build')['continue-on-error'])
        self.assertNotEqual(report(('build', 'Report Build result'), {'RESULT': 'failure'}), 0)
        self.assertFalse(condition(JOBS['test_lint']['if'], {'needs.build.result': 'failure'}))
        self.assertFalse(publish(build='failure'))

    def test_partial_cache_save_precedes_staging_and_new_attempt_can_restore_it(self):
        actions = JOBS['build']['steps']
        save = step('build', 'Save compilation independently of Test and lint')
        self.assertTrue(condition(save['if'], {'steps.quiesce.outcome': 'success'}, success=False))
        self.assertEqual(save['with']['path'].splitlines(),
                         ['${{ inputs.package-directory }}/.lake', '${{ runner.temp }}/lake-native-cache'])
        self.assertLess(actions.index(step('build', 'Build')), actions.index(save))
        self.assertLess(actions.index(save), actions.index(step('build', 'Stage completed native outputs')))
        restore = next(item for item in actions if item.get('id') == 'restore')['with']
        self.assertEqual(save['with']['key'], '${{ steps.restore.outputs.cache-primary-key }}')
        fields = {'runner.os': 'Linux', 'runner.arch': 'X64', 'github.sha': 'commit',
                  'github.run_id': 'run', 'github.run_attempt': '1',
                  'inputs.first-ci-cache': '', 'steps.first-ci.outputs.seed-key': 'seed'}
        def render(text):
            def evaluate(match):
                expression = re.sub(r'hashFiles\((?:[^()]|\([^()]*\))*\)',
                                    repr('input-hash'), match[1])
                expression = re.sub(r'\b(?:runner|github|inputs|steps)(?:\.[\w-]+)+',
                                    lambda token: repr(fields[token[0]]), expression)
                expression = expression.replace('&&', ' and ').replace('||', ' or ')
                return str(eval(expression, {'__builtins__': {}, 'format': str.format}, {}))
            return re.sub(r'\$\{\{\s*(.*?)\s*\}\}', evaluate, text)
        previous_key = render(restore['key'])
        fields['github.run_attempt'] = '2'
        self.assertNotEqual(render(restore['key']), previous_key)
        self.assertTrue(any(previous_key.startswith(prefix)
                            for prefix in render(restore['restore-keys']).splitlines()))

    def test_real_gnu_timeout_interrupts_lake_and_retains_completed_file(self):
        executable = shutil.which('timeout') or shutil.which('gtimeout')
        if not executable:
            self.skipTest('GNU timeout is unavailable; timeout status handling covered by workflow-shell stubs')
        version = subprocess.run([executable, '--version'], capture_output=True, text=True)
        if version.returncode or 'GNU coreutils' not in version.stdout:
            self.skipTest('available timeout is not GNU coreutils')
        with tempfile.TemporaryDirectory(prefix='lean-ci-real-cutoff-') as directory:
            root = Path(directory)
            (root / 'timeout').symlink_to(executable)
            compiler = root / 'lake'
            compiler.write_text(f'#!{sys.executable}\n' +
                                'from pathlib import Path\nimport signal\n'
                                'signal.signal(signal.SIGINT, lambda *_: exit(0))\n'
                                'Path("completed-module").write_text("completed before cutoff")\n'
                                'signal.pause()\n')
            compiler.chmod(0o755)
            result = subprocess.run(
                ['bash', '-e', '-o', 'pipefail', '-c',
                 'date() { printf "1000\\n"; }\n' + step('build', 'Build')['run']],
                cwd=root, env={**os.environ, 'PATH': directory + os.pathsep + os.environ['PATH'],
                               'BUILD_TARGETS': 'Aglib', 'BUILD_DEADLINE': '1001', 'RUNNER_TEMP': directory},
                capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 124, result.stderr)
            self.assertEqual((root / 'completed-module').read_text(), 'completed before cutoff')
            self.assertIn('timeout/kill status 124', result.stdout)

    def test_sigint_preserves_already_completed_process_output(self):
        with tempfile.TemporaryDirectory(prefix='lean-ci-interrupt-') as directory:
            root = Path(directory)
            source = ('from pathlib import Path\nimport signal\n'
                      'signal.signal(signal.SIGINT, lambda *_: exit(0))\n'
                      'Path("completed-module").write_text("completed before interrupt")\n'
                      'print("ready", flush=True)\n'
                      'signal.pause()\n')
            process = subprocess.Popen([sys.executable, '-c', source], cwd=root,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            try:
                self.assertEqual(process.stdout.readline(), 'ready\n')
                process.send_signal(signal.SIGINT)
                stdout, stderr = process.communicate(timeout=5)
                self.assertEqual(process.returncode, 0, stdout + stderr)
                self.assertEqual((root / 'completed-module').read_text(), 'completed before interrupt')
            finally:
                if process.poll() is None:
                    process.kill()
                    process.communicate()


class DependencyRecoveryAndNativeResources(unittest.TestCase):
    def test_recovery_runs_only_for_missing_or_failed_warm_cache(self):
        warm = step('test_lint', 'Warm dependency and native compilation outputs')
        self.assertTrue(warm['continue-on-error'])
        recovery = [step('test_lint', name) for name in (
            "Download this run's dependencies on cache miss",
            "Restore this run's dependencies on cache miss",
            'Recover Mathlib dependencies on cache miss')]
        for outcome, key, expected in (('success', 'warm-generation', False),
                                       ('success', '', True), ('failure', '', True),
                                       ('failure', 'partial-generation', True)):
            for action in recovery:
                values = {'steps.restore-cache.outcome': outcome,
                          'steps.restore-cache.outputs.cache-matched-key': key}
                self.assertEqual(condition(action['if'], values), expected)
                self.assertFalse(condition(action['if'], values, success=False))
                self.assertFalse(action.get('continue-on-error', False))
        self.assertEqual(recovery[0]['with'], {'name': 'build-dependencies',
                                              'path': '${{ runner.temp }}/build-dependencies'})
        self.assertEqual(recovery[2]['run'], step('build', 'Get Mathlib cache')['run'])
        actions = JOBS['test_lint']['steps']
        for before, after in zip(recovery, recovery[1:] + [step('test_lint', "Download this run's Build outputs")]):
            self.assertLess(actions.index(before), actions.index(after))
        self.assertLess(actions.index(step('test_lint', "Restore this run's native Build outputs")),
                        actions.index(step('test_lint', 'Verify Build outputs without compilation')))

    def test_same_run_native_handoff_covers_readonly_partial_restores(self):
        stage = step('build', 'Stage native dependencies for Test')
        upload = step('build', 'Upload native dependencies for Test')
        for action in (stage, upload):
            for outcome in ('success', 'failure', 'cancelled', 'skipped'):
                self.assertEqual(condition(action['if'], {'steps.build.outcome': outcome, 'steps.quiesce.outcome': 'success'}),
                                 outcome == 'success')
        self.assertEqual(upload['with']['name'], 'build-dependencies')
        self.assertTrue(upload['with']['overwrite'])
        self.assertEqual(upload['with']['if-no-files-found'], 'error')
        self.assertEqual(upload['with']['compression-level'], 0)
        with tempfile.TemporaryDirectory(prefix='native-dependency-handoff-') as directory:
            root = Path(directory)
            source = root / 'producer'
            for part in ('artifacts', 'outputs/Aglib', 'axiom-audit'):
                (source / part).mkdir(parents=True)
            (source / 'artifacts/dependency.olean').write_text('new unpublished output')
            (source / 'artifacts/native-tool').write_text('cached executable')
            (source / 'artifacts/native-tool').chmod(0o755)
            (source / 'outputs/Aglib/input.json').write_text('native mapping')
            (source / 'axiom-audit/checkout').write_text('not a dependency artifact')
            env = {**os.environ, 'RUNNER_TEMP': directory, 'LAKE_CACHE_DIR': str(source)}
            staged = subprocess.run(['bash', '-eo', 'pipefail', '-c', stage['run']],
                                    env=env, capture_output=True, text=True)
            self.assertEqual(staged.returncode, 0, staged.stderr)
            archive = root / 'build-dependencies.tar.zst'
            downloaded = root / 'build-dependencies'; downloaded.mkdir()
            archive.rename(downloaded / archive.name)
            target = root / 'consumer'; (target / 'artifacts').mkdir(parents=True)
            old = target / 'artifacts/dependency.olean'
            old.write_text('incomplete Actions restore'); old.chmod(0o444)
            restored = subprocess.run(['bash', '-eo', 'pipefail', '-c', step(
                'test_lint', "Restore this run's dependencies on cache miss")['run']],
                env={**env, 'LAKE_CACHE_DIR': str(target)}, capture_output=True, text=True)
            self.assertEqual(restored.returncode, 0, restored.stderr)
            self.assertEqual(old.read_text(), 'new unpublished output')
            self.assertTrue(os.access(target / 'artifacts/native-tool', os.X_OK))
            self.assertEqual((target / 'outputs/Aglib/input.json').read_text(), 'native mapping')
            self.assertFalse((target / 'axiom-audit').exists())
            self.assertFalse(downloaded.exists())

    def test_recovered_outputs_enable_checks_after_warm_cache_failure(self):
        values = {'needs.build.result': 'success', 'steps.restore-cache.outcome': 'failure',
                  'steps.lean-setup.outcome': 'success', 'steps.compiled.outcome': 'success',
                  'steps.tools.outcome': 'success'}
        for name in ('Lint', 'Audit production axioms'):
            self.assertTrue(condition(step('test_lint', name)['if'], values))
            self.assertFalse(condition(step('test_lint', name)['if'],
                                       {**values, 'steps.compiled.outcome': 'failure'}))

    def test_runner_does_not_interpret_posix_single_quotes(self):
        self.assertEqual(runner_arguments("bash -c 'echo success'"),
                         ['bash', '-c', "'echo", "success'"])

    def test_native_scope_retains_status_environment_and_old_memory_ceiling(self):
        shell = WORKFLOW['defaults']['run']['shell']
        with tempfile.TemporaryDirectory(prefix='native-resource-shell-') as directory:
            root = Path(directory)
            binary = root / 'bin'; binary.mkdir()
            (binary / 'getconf').write_text('#!/bin/sh\nif test "$1" = _PHYS_PAGES; then echo "$FIXTURE_PAGES"; else echo 4096; fi\n')
            (binary / 'nproc').write_text('#!/bin/sh\necho 4\n')
            (binary / 'sudo').write_text('''#!/usr/bin/env python3
import json,os,sys
args=sys.argv[1:]
assert args[0:2] == ['--preserve-env','systemd-run']
open(os.environ['TRACE'],'w').write(json.dumps(args))
index=args.index('/usr/bin/env')
os.execv(args[index],args[index:])
''')
            for file in binary.iterdir(): file.chmod(0o755)
            script = root / 'native step.sh'
            script.write_text('test "$VISIBLE_INPUT" = retained\ntest "$LEAN_NUM_THREADS" = 1\nexit "$STATUS"\n')
            for memory, expected in ((16384, 13824), (7168, 5120)):
                for status in (0, 7):
                    result = subprocess.run(runner_arguments(shell.format(script)), cwd=root,
                        env={**os.environ, 'PATH': str(binary) + ':' + os.environ['PATH'],
                             'FIXTURE_PAGES': str(memory * 256), 'STATUS': str(status),
                             'TRACE': str(root / 'trace'), 'VISIBLE_INPUT': 'retained',
                             'RUNNER_TEMP': str(root), 'GITHUB_RUN_ID': '123',
                             'GITHUB_RUN_ATTEMPT': '2', 'GITHUB_JOB': 'build'},
                        text=True, capture_output=True)
                    self.assertEqual(result.returncode, status, result.stderr)
                    args = json.loads((root / 'trace').read_text())
                    self.assertIn('--scope', args)
                    self.assertIn('--uid=' + str(os.getuid()), args)
                    self.assertIn('--gid=' + str(os.getgid()), args)
                    self.assertIn(f'--property=MemoryMax={expected}M', args)
                    self.assertIn('--property=MemorySwapMax=0', args)
                    unit = 'lean-ci-123-2-build-' + hashlib.sha256(str(script).encode()).hexdigest()[:20] + '.scope'
                    self.assertIn('--unit=' + unit, args)
                    marker = root / 'lean-ci-scopes/123-2-build' / unit
                    self.assertEqual(marker.read_text().strip(), unit)

    def test_each_library_keeps_native_weak_resource_arguments(self):
        for name, threads in (('aglib', 4), ('quillen-k-theory', 4), ('motivic', 4)):
            root = ROOT.parent / name
            if not root.exists():
                continue
            config = tomllib.loads((root / 'lakefile.toml').read_text())
            self.assertEqual(config['weakLeanArgs'], ['-M12800', f'-j{threads}'])


class NativeRunnerResources(unittest.TestCase):
    inputs = WORKFLOW.get('on', WORKFLOW.get(True))['workflow_call']['inputs']
    resource_names = {'CI_NATIVE_MEMORY_MIB': 'native-memory-mib',
                      'CI_LAKE_THREADS': 'lake-threads', 'CI_LINT_WORKERS': 'lint-workers'}

    def test_reusable_defaults_and_publish_isolation(self):
        self.assertEqual(tomllib.loads((ROOT / 'lakefile.toml').read_text())['weakLeanArgs'],
                         ['-M12800', '-j4'])
        self.assertEqual(self.inputs['runner-labels']['type'], 'string')
        self.assertEqual(json.loads(self.inputs['runner-labels']['default']), ['ubuntu-24.04'])
        for name, default in (('native-memory-mib', 13824), ('lake-threads', 1), ('lint-workers', 2), ('job-timeout-minutes', 360), ('build-lake-threads', 0)):
            self.assertEqual(self.inputs[name]['default'], default)
            self.assertIn(self.inputs[name]['type'], ('string', 'number'))
        for job in ('build', 'test_lint'):
            self.assertEqual(JOBS[job]['runs-on'], '${{ fromJSON(inputs.runner-labels) }}')
            self.assertEqual(JOBS[job]['timeout-minutes'], '${{ inputs.job-timeout-minutes }}')
            for variable, name in self.resource_names.items():
                self.assertEqual(JOBS[job]['env'][variable], '${{ inputs.' + name + ' }}')
        self.assertEqual(JOBS['upload_cache']['runs-on'], 'ubuntu-24.04')
        self.assertNotIn('defaults', JOBS['upload_cache'])
        for variable in self.resource_names:
            self.assertNotIn(variable, JOBS['upload_cache'].get('env', {}))
            self.assertNotIn(variable, WORKFLOW.get('env', {}))
            self.assertNotIn('$' + variable, WORKFLOW['defaults']['run']['shell'])

    @staticmethod
    def workflow_value(expression, values):
        expression = expression.removeprefix('${{').removesuffix('}}').strip()
        expression = re.sub(r'(?:github|inputs)\.[\w-]+',
                            lambda match: repr(values[match[0]]), expression)
        return eval(expression.replace('&&', ' and ').replace('||', ' or '),
                    {'__builtins__': {}}, {})

    def test_only_explicit_main_ec2_dispatch_selects_trial_resources(self):
        caller = yaml.safe_load((ROOT / '.github/workflows/ci.yml').read_text())
        dispatch = caller.get('on', caller.get(True))['workflow_dispatch']['inputs']
        for name, options, default in (('runner-profile', ['hosted', 'ec2'], 'hosted'),
                                       ('ec2-job-minutes', ['150', '90'], '150'),
                                       ('ec2-build-lake-threads', ['4', '8'], '4')):
            self.assertEqual(dispatch[name]['type'], 'choice')
            self.assertEqual(dispatch[name]['default'], default)
            self.assertEqual(dispatch[name]['options'], options)
        settings = caller['jobs']['lean']['with']
        self.assertEqual(settings['build-targets'], 'Aglib')
        self.assertEqual(caller['concurrency'], {'group': 'Aglib CI-${{ github.ref }}',
                                                'cancel-in-progress': False, 'queue': 'max'})
        for ref in ('refs/heads/main', 'refs/heads/topic', 'refs/pull/1/merge'):
            for event in ('push', 'workflow_dispatch', 'pull_request'):
                for profile in ('', 'hosted', 'ec2'):
                    for minutes in ('', '150', '90', 'invalid'):
                        for threads in ('', '4', '8', 'invalid'):
                            expected_ec2 = ref == 'refs/heads/main' and event == 'workflow_dispatch' and profile == 'ec2'
                            values = {'github.ref': ref, 'github.event_name': event, 'inputs.runner-profile': profile,
                                      'inputs.ec2-job-minutes': minutes, 'inputs.ec2-build-lake-threads': threads}
                            names = ('native-memory-mib', 'lake-threads', 'lint-workers',
                                     'job-timeout-minutes', 'build-lake-threads')
                            selected = {name: self.workflow_value(settings[name], values)
                                        for name in ('runner-labels', *names)}
                            self.assertEqual(json.loads(selected.pop('runner-labels')),
                                ['self-hosted', 'linux', 'x64', 'aglib-ec2-pilot'] if expected_ec2 else ['ubuntu-24.04'])
                            self.assertEqual(selected, dict(zip(names,
                                (57344, 4, 4, 90 if minutes == '90' else 150, 8 if threads == '8' else 4)
                                if expected_ec2 else (13824, 1, 2, 360, 0))))

    def test_build_runtime_override_is_production_step_only_and_preserves_fallback(self):
        production = step('build', 'Build')
        self.assertEqual(self.inputs['build-lake-threads']['type'], 'number')
        for job in ('build', 'test_lint', 'upload_cache'):
            for action in JOBS[job]['steps']:
                if action is not production:
                    self.assertNotIn('CI_LAKE_THREADS', action.get('env', {}))
        for default, override, expected in ((1, 0, 1), (4, 0, 4), (4, 4, 4), (4, 8, 8)):
            selected = self.workflow_value(production['env']['CI_LAKE_THREADS'],
                                          {'inputs.build-lake-threads': override, 'inputs.lake-threads': default})
            self.assertEqual(selected, expected)
            # Exercise the actual .NET-formatted shell with the step's effective environment.
            result, arguments = self.run_scope('build', CI_LAKE_THREADS=selected, CI_LINT_WORKERS=4)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('LEAN_NUM_THREADS=' + str(expected), arguments)
            self.assertIn('CI_LINT_WORKERS=4', arguments)
            # Job-level defaults, shared with Test, do not read the Build-only input.
            for job in ('build', 'test_lint'):
                self.assertEqual(JOBS[job]['env']['CI_LAKE_THREADS'], '${{ inputs.lake-threads }}')

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='native-resource-inputs-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        binary = self.root / 'bin'
        binary.mkdir()
        (binary / 'getconf').write_text('#!/bin/sh\nif test "$1" = _PHYS_PAGES; then echo "$FIXTURE_PAGES"; else echo 4096; fi\n')
        (binary / 'nproc').write_text('#!/bin/sh\necho 16\n')
        (binary / 'sudo').write_text("""#!/usr/bin/env python3
import json,os,sys
args=sys.argv[1:]
assert args[0:2] == ['--preserve-env','systemd-run']
open(os.environ['TRACE'],'w').write(json.dumps(args))
index=args.index('/usr/bin/env')
os.execv(args[index],args[index:])
""")
        for file in binary.iterdir():
            file.chmod(0o755)
        self.script = self.root / 'native step.sh'
        self.script.write_text('test "$VISIBLE_INPUT" = retained\n'
                               'test "$LEAN_NUM_THREADS" = "$EXPECTED_THREADS"\n'
                               'test "${CI_LINT_WORKERS:-}" = "$EXPECTED_LINT_WORKERS"\n'
                               'exit "$STATUS"\n')

    def run_scope(self, job, memory=65536, status=0, **resources):
        shell = JOBS[job].get('defaults', WORKFLOW['defaults'])['run']['shell']
        trace = self.root / 'trace'
        trace.unlink(missing_ok=True)
        environment = {key: value for key, value in os.environ.items()
                       if key not in (*self.resource_names, 'LEAN_NUM_THREADS')}
        if job != 'upload_cache':
            environment.update({variable: str(self.inputs[name]['default'])
                                for variable, name in self.resource_names.items()})
        environment.update({key: str(value) for key, value in resources.items()})
        environment.update({'PATH': str(self.root / 'bin') + ':' + os.environ['PATH'],
                            'FIXTURE_PAGES': str(memory * 256), 'STATUS': str(status),
                            'TRACE': str(trace), 'VISIBLE_INPUT': 'retained',
                            'EXPECTED_THREADS': environment.get('CI_LAKE_THREADS', '1'),
                            'EXPECTED_LINT_WORKERS': environment.get('CI_LINT_WORKERS', ''),
                            'RUNNER_TEMP': str(self.root), 'GITHUB_RUN_ID': '123',
                            'GITHUB_RUN_ATTEMPT': '2', 'GITHUB_JOB': job})
        # The runner applies .NET composite formatting before argument parsing.
        # Python's formatter also rejects unescaped Bash parameter braces here.
        result = subprocess.run(runner_arguments(shell.format(self.script)),
                                cwd=self.root, env=environment, text=True, capture_output=True, timeout=5)
        return result, json.loads(trace.read_text()) if trace.exists() else None

    def test_native_inputs_memory_clamp_status_environment_and_scope_identity(self):
        for job in ('build', 'test_lint', 'upload_cache'):
            cases = [(16384, {}, 13824), (7168, {}, 5120)]
            if job != 'upload_cache':
                ec2 = dict(CI_NATIVE_MEMORY_MIB=57344, CI_LAKE_THREADS=4, CI_LINT_WORKERS=4)
                cases += [(65536, ec2, 57344), (32768, ec2, 30720),
                          (65536, {**ec2, 'CI_NATIVE_MEMORY_MIB': '9' * 40}, 63488)]
            for memory, resources, expected in cases:
                for status in (0, 7):
                    with self.subTest(job=job, memory=memory, resources=resources, status=status):
                        result, args = self.run_scope(job, memory, status, **resources)
                        self.assertEqual(result.returncode, status, result.stderr)
                        for argument in ('--scope', '--property=MemorySwapMax=0',
                                         f'--property=MemoryMax={expected}M',
                                         '--uid=' + str(os.getuid()), '--gid=' + str(os.getgid())):
                            self.assertIn(argument, args)
                        unit = f'lean-ci-123-2-{job}-' + hashlib.sha256(str(self.script).encode()).hexdigest()[:20] + '.scope'
                        self.assertIn('--unit=' + unit, args)
                        self.assertEqual((self.root / f'lean-ci-scopes/123-2-{job}' / unit).read_text().strip(), unit)

    def test_invalid_resource_inputs_and_insufficient_ram_fail_before_scope_launch(self):
        for job in ('build', 'test_lint'):
            for variable in self.resource_names:
                for value in ('', '0', '-1', '1.5', 'abc', '$(touch injected)'):
                    with self.subTest(job=job, variable=variable, value=value):
                        result, args = self.run_scope(job, **{variable: value})
                        self.assertEqual(result.returncode, 2, result.stderr)
                        self.assertIn('must be positive integers', result.stderr)
                        self.assertIsNone(args)
                        self.assertFalse((self.root / 'injected').exists())
            for memory in (1024, 2048):
                result, args = self.run_scope(job, memory)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn('runner reserve', result.stderr)
                self.assertIsNone(args)


class ResourceMonitorIntegration(unittest.TestCase):
    def test_diagnostics_are_optional_outside_scopes_and_follow_cache_saves(self):
        for job in ('build', 'test_lint'):
            actions = JOBS[job]['steps']
            start = step(job, 'Start native resource sampler')
            stop = step(job, 'Stop native resource sampler')
            upload = step(job, 'Upload native resource observations')
            checkout = next(action for action in actions if action.get('uses', '').startswith('actions/checkout@'))
            self.assertEqual(actions.index(start), actions.index(checkout) + 1)
            for action in (start, stop):
                self.assertEqual(action['shell'], 'bash')
                self.assertTrue(action['continue-on-error'])
                self.assertEqual(action['timeout-minutes'], 1)
                self.assertEqual(action['working-directory'], '${{ inputs.package-directory }}')
                with tempfile.TemporaryDirectory(prefix='ci-no-resource-helper-') as directory:
                    result = subprocess.run(['bash', '-eo', 'pipefail', '-c', action['run']],
                                            cwd=directory, capture_output=True, text=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(start['env']['JOB_TIMEOUT_MINUTES'], '${{ inputs.job-timeout-minutes }}')
            self.assertEqual(start['env']['CI_RESOURCE_RUNNER_LABELS'], '${{ inputs.runner-labels }}')
            for action in (stop, upload):
                self.assertTrue(condition(action['if'], {}, success=False, cancelled=True))
                self.assertTrue(action['continue-on-error'])
            for action in actions:
                if action.get('name', '').startswith(('Save ', 'Pack ')):
                    self.assertLess(actions.index(action), actions.index(stop))
            self.assertLess(actions.index(stop), actions.index(upload))
            self.assertTrue(upload['uses'].startswith('actions/upload-artifact@'))
            self.assertEqual(upload['with']['if-no-files-found'], 'ignore')
            self.assertEqual(upload['with']['retention-days'], 7)
            for field in ('github.run_id', 'github.run_attempt', 'github.job'):
                self.assertIn(field, upload['with']['name'])
                self.assertIn(field, upload['with']['path'])
        self.assertEqual(JOBS['build']['steps'][0]['name'], 'Set Build deadline')
        self.assertNotIn('Start native resource sampler',
                         [action.get('name') for action in JOBS['upload_cache']['steps']])


class NativeScopeQuiescence(unittest.TestCase):
    name = "Quiesce this job's native scopes before cache saving"

    def test_cancellation_quiesces_before_save_and_failed_quiescence_blocks_cache_readers(self):
        for job, save in (('build', 'Save compilation independently of Test and lint'),
                          ('test_lint', 'Save completed Test compilation')):
            actions = JOBS[job]['steps']
            cleanup = step(job, self.name)
            self.assertEqual(cleanup['shell'], 'bash')  # Outside the scopes it stops.
            self.assertFalse(cleanup.get('continue-on-error', False))
            self.assertTrue(condition(cleanup['if'], {}, success=False, cancelled=True))
            self.assertLess(actions.index(cleanup), actions.index(step(job, save)))
            for outcome in ('success', 'failure', 'skipped', 'cancelled'):
                values = {'steps.quiesce.outcome': outcome, 'steps.build.outcome': 'failure'}
                self.assertEqual(condition(step(job, save)['if'], values,
                                           success=False, cancelled=True), outcome == 'success')
                if job == 'build':
                    self.assertEqual(condition(step(job, 'Stage completed native outputs')['if'],
                                               values, success=False), outcome == 'success')

    def run_cleanup(self, root, *, failed=False, collected_during_stop=False):
        binary = root / 'bin'; binary.mkdir(exist_ok=True)
        (binary / 'sudo').write_text('#!/bin/sh\nexec "$@"\n')
        (binary / 'systemctl').write_text(f'#!{sys.executable}\n' + r'''
import json,os,signal,sys,time
from pathlib import Path
root=Path(os.environ['FIXTURE_ROOT']); args=sys.argv[1:]
with (root/'calls').open('a') as stream: stream.write(json.dumps(args)+'\n')
if os.environ.get('FIXTURE_FAIL') == '1': sys.exit(7)
units=json.loads((root/'units.json').read_text()); unit=args[-1]; data=units.get(unit)
if (root/'collected').exists(): data=None
if args[0]=='show':
    if '--property=LoadState' in args: print('loaded' if data else 'not-found')
    else: print('inactive' if not data or Path(data['stopped']).exists() else 'active')
elif args[0]=='stop':
    if os.environ.get('FIXTURE_COLLECTED') == '1':
        (root/'collected').touch(); sys.exit(5)
    assert data, 'must not stop an unknown or unrecorded unit'
    os.kill(data['pid'],signal.SIGTERM)
    until=time.monotonic()+2
    while not Path(data['stopped']).exists():
        if time.monotonic()>until: sys.exit(8)
        time.sleep(.01)
else: sys.exit(9)
''')
        for file in binary.iterdir(): file.chmod(0o755)
        return subprocess.run(['bash', '-eo', 'pipefail', '-c', step('build', self.name)['run']],
                              env={**os.environ, 'PATH': str(binary) + ':' + os.environ['PATH'],
                                   'RUNNER_TEMP': str(root), 'GITHUB_RUN_ID': '123',
                                   'GITHUB_RUN_ATTEMPT': '2', 'GITHUB_JOB': 'build',
                                   'FIXTURE_ROOT': str(root), 'FIXTURE_FAIL': '1' if failed else '0',
                                   'FIXTURE_COLLECTED': '1' if collected_during_stop else '0'},
                              text=True, capture_output=True, timeout=5)

    def test_live_owned_cache_writer_stops_and_other_job_keeps_running(self):
        with tempfile.TemporaryDirectory(prefix='ci-scope-writer-') as directory:
            root = Path(directory)
            writer = ('import signal,sys,time\nfrom pathlib import Path\n'
                      'output,stopped=map(Path,sys.argv[1:])\n'
                      'def finish(*_):\n stopped.write_text("stopped"); sys.exit(0)\n'
                      'signal.signal(signal.SIGTERM,finish)\n'
                      'while True:\n output.write_text(str(time.monotonic())); time.sleep(.01)\n')
            owned = subprocess.Popen([sys.executable, '-c', writer, str(root/'owned-output'), str(root/'owned-stopped')])
            foreign = subprocess.Popen([sys.executable, '-c', writer, str(root/'foreign-output'), str(root/'foreign-stopped')])
            try:
                until = time.monotonic() + 2
                while not all((root/name).exists() for name in ('owned-output', 'foreign-output')):
                    self.assertLess(time.monotonic(), until)
                    time.sleep(.01)
                unit = 'lean-ci-123-2-build-owned.scope'
                markers = root / 'lean-ci-scopes/123-2-build'; markers.mkdir(parents=True)
                (markers / unit).write_text(unit + '\n')
                gone = 'lean-ci-123-2-build-already-collected.scope'
                (markers / gone).write_text(gone + '\n')
                other = root / 'lean-ci-scopes/999-1-test'; other.mkdir()
                foreign_unit = 'lean-ci-999-1-test-foreign.scope'
                (other/foreign_unit).write_text(foreign_unit+'\n')
                (root/'units.json').write_text(json.dumps({
                    unit: {'pid': owned.pid, 'stopped': str(root/'owned-stopped')},
                    foreign_unit: {'pid': foreign.pid, 'stopped': str(root/'foreign-stopped')}}))
                result = self.run_cleanup(root)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(owned.wait(timeout=2), 0)
                completed = (root/'owned-output').read_bytes()
                time.sleep(.05)
                self.assertEqual((root/'owned-output').read_bytes(), completed)
                self.assertIsNone(foreign.poll())
                self.assertFalse((root/'foreign-stopped').exists())
                calls = [json.loads(line) for line in (root/'calls').read_text().splitlines()]
                self.assertEqual([c[-1] for c in calls if c[0]=='stop'], [unit])
                self.assertNotIn(foreign_unit, [c[-1] for c in calls])
            finally:
                for process in (owned, foreign):
                    if process.poll() is None: process.terminate()
                    process.wait(timeout=2)

    def test_unexpected_marker_and_systemctl_failure_are_not_masked(self):
        for invalid, failed in ((True, False), (False, True)):
            with self.subTest(invalid=invalid), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                markers = root/'lean-ci-scopes/123-2-build'; markers.mkdir(parents=True)
                unit = 'foreign.scope' if invalid else 'lean-ci-123-2-build-owned.scope'
                (markers/unit).write_text(unit+'\n')
                (root/'units.json').write_text('{}')
                result = self.run_cleanup(root, failed=failed)
                self.assertNotEqual(result.returncode, 0)
                calls = (root/'calls').read_text() if (root/'calls').exists() else ''
                self.assertNotIn('"stop"', calls)

    def test_scope_collected_between_query_and_stop_is_already_quiescent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            markers = root/'lean-ci-scopes/123-2-build'; markers.mkdir(parents=True)
            unit = 'lean-ci-123-2-build-finished.scope'
            (markers/unit).write_text(unit+'\n')
            (root/'units.json').write_text(json.dumps({unit: {'stopped': str(root/'finished')}}))
            result = self.run_cleanup(root, collected_during_stop=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue((root/'collected').exists())


class CheckerBoundaryAndLintTimeout(unittest.TestCase):
    def test_build_has_no_checker_dependency_or_helper_targets(self):
        self.assertEqual(set(JOBS), {'build', 'test_lint', 'upload_cache'})
        self.assertEqual(JOBS['upload_cache']['name'], 'Publish cache')
        build = step('build', 'Build')
        self.assertNotIn('if', build)
        for item in JOBS['build']['steps']:
            command = item.get('run', '')
            for forbidden in ('axiom-audit', 'batteries/runLinter', 'mathlib/lint-style',
                              'mathlib/mk_all', 'CHECK_TARGETS', 'steps.tools',
                              'steps.imports', 'steps.style'):
                self.assertNotIn(forbidden, command + item.get('if', ''), item.get('name'))
        result = subprocess.run(
            ['bash', '-e', '-o', 'pipefail', '-c', 'lake() { printf "%s\\n" "$*"; }\n'
             'timeout() { shift 3; "$@"; }\n' + build['run']],
            env={**os.environ, 'BUILD_TARGETS': 'R5Lab Essays', 'CHECK_TARGETS': 'Checks',
                 'BUILD_DEADLINE': '2000000000', 'RUNNER_TEMP': '/fixture'}, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), ['build --rehash R5Lab Essays -o /fixture/outputs.jsonl'])

    def test_optional_check_targets_default_empty_and_are_built_only_in_test(self):
        inputs = WORKFLOW.get('on', WORKFLOW.get(True))['workflow_call']['inputs']
        self.assertEqual(inputs['check-targets'], {'type': 'string', 'default': ''})
        tools = step('test_lint', 'Prepare check tools')
        self.assertEqual(tools['env'], {'CHECK_TARGETS': '${{ inputs.check-targets }}'})
        steps = JOBS['test_lint']['steps']
        self.assertLess(steps.index(step('test_lint', 'Verify Build outputs without compilation')),
                        steps.index(tools))
        self.assertLess(steps.index(tools), steps.index(step('test_lint', 'Test')))
        for helpers, expected in (('', []), ('   ', []), ('Checks', ['Checks']),
                                  ('Checks ExtraChecks', ['Checks', 'ExtraChecks'])):
            with self.subTest(helpers=helpers):
                result = subprocess.run(
                    ['bash', '-e', '-o', 'pipefail', '-c',
                     'lake() { printf "%s\\n" "$@"; }\n' + tools['run']],
                    env={**os.environ, 'CHECK_TARGETS': helpers}, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.splitlines(), [
                    'build', 'batteries/runLinter', 'mathlib/lint-style', 'mathlib/mk_all', *expected])

    def test_checker_failures_stay_in_test_and_source_checks_collect_feedback(self):
        names = ['Prepare check tools', 'Check generated library entries', 'Mathlib text style']
        steps = [item for item in JOBS['test_lint']['steps'] if item.get('name') in names]
        self.assertEqual([item['name'] for item in steps], names)
        self.assertTrue(all(item['continue-on-error'] for item in steps))
        self.assertEqual(sum(item.get('name') == 'Mathlib text style'
                             for job in JOBS.values() for item in job['steps']), 1)
        mock = r"""
lake() {
  printf '%s\n' "$*" >> "$TRACE"
  if test "$1" = build; then return "$TOOLS_STATUS"; fi
  if test "$3" = mathlib/mk_all; then return "$IMPORTS_STATUS"; fi
  if test "$3" = mathlib/lint-style; then return "$STYLE_STATUS"; fi
  return 99
}
"""
        for tools, imports, style in ((0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 1)):
            with self.subTest(tools=tools, imports=imports, style=style), \
                    tempfile.TemporaryDirectory(prefix='lean-ci-checkers-') as directory:
                trace = Path(directory) / 'trace'
                values = {f'steps.{name}.outcome': 'skipped' for name in ('tools', 'imports', 'style')}
                for item in steps:
                    if 'if' in item and not condition(item['if'], values):
                        continue
                    result = subprocess.run(
                        ['bash', '-e', '-o', 'pipefail', '-c', mock + item['run']],
                        env={**os.environ, 'BUILD_TARGETS': 'Aglib Quillen', 'CHECK_TARGETS': 'Checks',
                             'TRACE': str(trace), 'TOOLS_STATUS': str(tools),
                             'IMPORTS_STATUS': str(imports), 'STYLE_STATUS': str(style)},
                        capture_output=True, text=True)
                    values[f"steps.{item['id']}.outcome"] = 'success' if result.returncode == 0 else 'failure'
                commands = trace.read_text().splitlines()
                self.assertEqual(commands[0], 'build batteries/runLinter mathlib/lint-style mathlib/mk_all Checks')
                self.assertEqual(commands[1:], [] if tools else [
                    '--no-build exe mathlib/mk_all --lib Aglib --check',
                    '--no-build exe mathlib/mk_all --lib Quillen --check',
                    '--no-build exe mathlib/lint-style Aglib Quillen'])
                self.assertEqual(report(('build', 'Report Build result'), {'RESULT': 'success'}), 0)
                outcomes = dict.fromkeys(('COMPILED', 'TEST', 'LINT', 'AXIOMS'), 'success')
                outcomes.update({name.upper(): values[f'steps.{name}.outcome']
                                 for name in ('tools', 'imports', 'style')})
                failed = bool(tools or imports or style)
                self.assertEqual(report(('test_lint', 'Report Test, lint and axiom results'), outcomes) != 0,
                                 failed)
                self.assertEqual(publish(tests='failure' if failed else 'success'), not failed)

    def test_lint_only_retries_one_timeout_and_preserves_final_status(self):
        lint = step('test_lint', 'Lint')
        self.assertEqual(lint['timeout-minutes'], 45)
        self.assertTrue(lint['continue-on-error'])
        mock = r'''
count=0
timeout() {
  count=$((count + 1))
  printf '%s\n' "$*" >> "$TRACE"
  if test "$count" -eq 1; then return "$FIRST"; fi
  return "$SECOND"
}
'''
        for first, second, expected, attempts in (
                (0, 0, 0, 1), (1, 0, 1, 1), (124, 0, 0, 2),
                (124, 124, 124, 2), (124, 1, 1, 2), (137, 0, 137, 1), (143, 0, 143, 1)):
            with self.subTest(first=first, second=second):
                with tempfile.TemporaryDirectory(prefix='lean-ci-timeout-') as directory:
                    trace = Path(directory) / 'trace'
                    result = subprocess.run(
                        ['bash', '-e', '-o', 'pipefail', '-c', mock + lint['run']],
                        env={**os.environ, 'BUILD_TARGETS': 'Aglib Quillen', 'TRACE': str(trace),
                             'FIRST': str(first), 'SECOND': str(second), 'GITHUB_WORKSPACE': ''},
                        capture_output=True, text=True, check=False)
                    self.assertEqual(result.returncode, expected, result.stderr)
                    self.assertEqual(trace.read_text().splitlines(), [
                        '--kill-after=30s 20m env LEAN_ABORT_ON_PANIC=1 lake --no-build lint Aglib Quillen -- --trace'
                    ] * attempts)

    def test_lint_helper_preserves_roots_panic_mode_and_status(self):
        mock = r'''
timeout() { shift 2; "$@"; }
lake() { echo 'unexpected native fallback' >&2; return 99; }
export -f lake
'''
        for status, attempts in ((0, 1), (1, 1), (124, 2), (137, 1)):
            with self.subTest(status=status):
                with tempfile.TemporaryDirectory(prefix='lean-ci-lint-helper-') as directory:
                    workspace = Path(directory) / 'workspace with spaces'
                    helper = workspace / '.github/lint/run.sh'
                    helper.parent.mkdir(parents=True)
                    package = workspace / 'lean package'
                    package.mkdir()
                    helper.write_text(
                        'printf "panic:%s\\n" "$LEAN_ABORT_ON_PANIC" >> "$TRACE"\n'
                        'printf "cwd:%s\\n" "$PWD" >> "$TRACE"\n'
                        'printf "root:%s\\n" "$@" >> "$TRACE"\n'
                        'exit "$HELPER_STATUS"\n')
                    trace = Path(directory) / 'trace'
                    result = subprocess.run(
                        ['bash', '-e', '-o', 'pipefail', '-c', mock + step('test_lint', 'Lint')['run']],
                        env={**os.environ, 'GITHUB_WORKSPACE': str(workspace),
                             'BUILD_TARGETS': 'Aglib Quillen', 'TRACE': str(trace),
                             'HELPER_STATUS': str(status)},
                        cwd=package,
                        capture_output=True, text=True, check=False)
                    self.assertEqual(result.returncode, status, result.stderr)
                    self.assertEqual(trace.read_text().splitlines(),
                                     ['panic:1', f'cwd:{package.resolve()}', 'root:Aglib', 'root:Quillen'] * attempts)
                    self.assertNotIn('unexpected native fallback', result.stderr)


class PublishedDependencyTransport(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='native-dependency-cache-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / 'lean-toolchain').write_text('fixture\n')
        self.domain = 'Linux-X64-' + hashlib.sha256(b'fixture\n').hexdigest()[:16]
        self.pin, self.seed = '1' * 40, '2' * 40
        self.releases = []
        self.package = 'Aglib'
        self.dependencies = [{'name': self.package, 'type': 'git', 'inherited': True,
                              'url': 'https://github.com/kangxyz/aglib.git', 'rev': self.pin}]

    def release(self, revision, *, changes=None, legacy=False, unsafe=False):
        index = len(self.releases) + 1
        name = (f'lake-native-cache-{index}-1.tar' if legacy else
                f'lake-native-cache-{self.domain}-{index}-1.tar')
        metadata = dict(repository='kangxyz/aglib', revision=revision, domain=self.domain,
                        package=self.package.strip('«»'), compiler='Lean fixture')
        metadata.update(changes or {})
        with tarfile.open(self.root / name, 'w') as archive:
            entries = {'./outputs.jsonl': b'fixture native mappings'}
            if not legacy:
                entries['./producer.json'] = json.dumps(metadata).encode()
            if unsafe:
                entries['../escape'] = b'not a native staging member'
            for path, content in entries.items():
                member = tarfile.TarInfo(path)
                member.size = len(content)
                archive.addfile(member, io.BytesIO(content))
        release = dict(id=index, draft=False, tag_name='lean-native-' + revision,
                       target_commitish=revision, assets=[dict(name=name, created_at=str(index))])
        self.releases.append(release)
        return release

    def run_restore(self, *, offline=False, layered=False, reject_revision=""):
        if layered:
            helper = self.root / '.github/ci-cache/stage.py'
            helper.parent.mkdir(parents=True, exist_ok=True)
            helper.write_text('import json, os, pathlib, sys\n'
                              'stage=pathlib.Path(sys.argv[sys.argv.index("--staging")+1])\n'
                              'revision=json.loads((stage/"producer.json").read_text())["revision"]\n'
                              'with open(os.environ["TRACE"], "a") as f: f.write("verify:"+revision+"\\n")\n'
                              'sys.exit(17 if revision==os.environ["REJECT_REVISION"] else 0)\n')
        (self.root / 'lake-manifest.json').write_text(json.dumps({'packages': self.dependencies}))
        exact = next((r for r in self.releases if r['tag_name'] == 'lean-native-' + self.pin), None)
        (self.root / 'exact.json').write_text(json.dumps(exact))
        (self.root / 'recent.json').write_text(json.dumps(list(reversed(self.releases))))
        mock = r"""
lean() { printf 'Lean fixture\n'; }
gh() {
  printf 'gh:%s\n' "$*" >> "$TRACE"
  test "$OFFLINE" = 0 || return 1
  if test "$1" = api; then
    if [[ "$2" == */tags/* ]]; then cat "$FIXTURE/exact.json";
    else cat "$FIXTURE/recent.json"; fi
  else
    cp "$FIXTURE/$7" "$9/$7"
  fi
}
lake() { printf 'lake:%s\n' "$4" >> "$TRACE"; }
"""
        result = subprocess.run(
            ['bash', '-e', '-o', 'pipefail', '-c', mock + step(
                'build', 'Restore published native dependency caches')['run']],
            cwd=self.root, env={**os.environ, 'RUNNER_TEMP': str(self.root), 'RUNNER_OS': 'Linux',
                               'RUNNER_ARCH': 'X64', 'TRACE': str(self.root / 'trace'),
                               'FIXTURE': str(self.root), 'OFFLINE': str(int(offline)),
                               'LAYERED_CACHE': 'true' if layered else '', 'REJECT_REVISION': reject_revision},
            capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        trace = (self.root / 'trace').read_text().splitlines() if (self.root / 'trace').exists() else []
        return result.stdout, trace

    def test_exact_pin_wins_and_inherited_dependency_is_not_skipped(self):
        self.release(self.pin)
        self.release(self.seed)
        output, trace = self.run_restore()
        self.assertIn('producer ' + self.pin, output)
        self.assertEqual([line for line in trace if line.startswith('lake:')], ['lake:Aglib'])
        self.assertEqual(sum('release download' in line for line in trace), 1)

    def test_package_scope_preserves_quoted_hyphenated_selectors(self):
        self.package = '«quillen-k-theory»'
        self.dependencies[0]['name'] = self.package
        self.release(self.pin)
        _, trace = self.run_restore()
        self.assertIn('lake:«quillen-k-theory»', trace)

    def test_recent_legacy_native_asset_can_seed_a_missing_pin(self):
        self.release(self.seed, legacy=True)
        output, trace = self.run_restore()
        self.assertIn('legacy native seed', output)
        self.assertIn('producer ' + self.seed + ' for pin ' + self.pin, output)
        self.assertIn('lake:Aglib', trace)

    def test_incompatible_or_unsafe_exact_asset_falls_back_before_unstage(self):
        cases = [{'repository': 'other/project'}, {'revision': self.seed},
                 {'package': 'Foreign'}, {'domain': 'other-platform'}, {'compiler': 'other-compiler'}, None]
        for changes in cases:
            with self.subTest(changes=changes):
                self.releases = []
                (self.root / 'trace').unlink(missing_ok=True)
                self.release(self.pin, changes=changes, unsafe=changes is None)
                self.release(self.seed)
                output, trace = self.run_restore()
                self.assertIn('producer ' + self.seed + ' for pin ' + self.pin, output)
                self.assertEqual([line for line in trace if line.startswith('lake:')], ['lake:Aglib'])
                self.assertFalse((self.root / 'escape').exists())

    def test_layered_seed_verification_skips_invalid_candidate_before_import(self):
        self.release(self.pin)
        self.release(self.seed)
        original = {release['assets'][0]['name']: (self.root / release['assets'][0]['name']).read_bytes()
                    for release in self.releases}
        output, trace = self.run_restore(layered=True, reject_revision=self.pin)
        self.assertIn('invalid native module archive', output)
        self.assertIn('producer ' + self.seed, output)
        self.assertEqual([line for line in trace if line.startswith(('verify:', 'lake:'))],
                         ['verify:' + self.pin, 'verify:' + self.seed, 'lake:Aglib'])
        for name, data in original.items():
            self.assertEqual((self.root / name).read_bytes(), data)
        self.assertFalse(any(' delete ' in line or ' upload ' in line for line in trace))

    def test_optional_download_outage_retains_ordinary_build_fallback(self):
        output, trace = self.run_restore(offline=True)
        self.assertIn('ordinary incremental build', output)
        self.assertFalse(any(line.startswith('lake:') for line in trace))

    def test_foreign_repository_and_non_git_dependencies_are_not_downloaded(self):
        self.dependencies = [dict(self.dependencies[0], url='https://github.com/other/aglib.git'),
                             dict(self.dependencies[0], type='path')]
        _, trace = self.run_restore()
        self.assertEqual(trace, [])


class RootSelectionAndPublication(unittest.TestCase):
    def test_lint_commands_pass_all_roots_as_native_arguments(self):
        for job, name, expected in (
                ('test_lint', 'Lint', ['--no-build', 'lint', 'Aglib', 'Quillen', '--', '--trace']),
                ('test_lint', 'Mathlib text style', ['--no-build', 'exe', 'mathlib/lint-style', 'Aglib', 'Quillen'])):
            with self.subTest(step=name):
                result = subprocess.run(
                    ['bash', '-e', '-o', 'pipefail', '-c',
                     'lake() { printf "%s\\n" "$@"; }\n'
                     'timeout() { shift; shift; shift; shift; "$@"; }\n' + step(job, name)['run']],
                    env={**os.environ, 'BUILD_TARGETS': 'Aglib Quillen', 'GITHUB_WORKSPACE': ''},
                    capture_output=True, text=True, check=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.splitlines(), expected)

    def test_new_release_includes_asset_and_never_becomes_latest(self):
        self.run_publication(exists=False)

    def test_existing_release_appends_asset(self):
        self.run_publication(exists=True)

    def test_existing_immutable_asset_is_preserved(self):
        self.run_publication(exists=True, asset_exists=True)

    def test_release_failures_are_not_masked(self):
        for exists in (False, True):
            with self.subTest(exists=exists):
                self.run_publication(exists=exists, status=1)

    def run_publication(self, *, exists, status=0, asset_exists=False):
        with tempfile.TemporaryDirectory(prefix='lean-ci-release-') as directory:
            root = Path(directory)
            producer = {'repository': 'fixture/aglib', 'revision': '0123456',
                        'domain': 'Linux-X64-fixture'}
            content = json.dumps(producer).encode()
            with tarfile.open(root / 'lake-native-cache.tar', 'w') as archive:
                member = tarfile.TarInfo('./producer.json')
                member.size = len(content)
                archive.addfile(member, io.BytesIO(content))
            mock = r'''
gh() {
  printf '%s\n' "$*" >> "$TRACE"
  if test "$2" = view; then
    test "$VIEW_STATUS" = 0 || return "$VIEW_STATUS"
    printf '%s\n' "$EXISTING_ASSET"
    return 0
  fi
  test -s "$ASSET" || return 99
  return "$PUBLISH_STATUS"
}
'''
            result = subprocess.run(
                ['bash', '-e', '-o', 'pipefail', '-c',
                 mock + step('upload_cache', 'Publish staged compilation')['run']],
                cwd=root, env={**os.environ, 'TRACE': directory + '/trace',
                               'VIEW_STATUS': '0' if exists else '1',
                               'PUBLISH_STATUS': str(status), 'GITHUB_RUN_ID': '1', 'GITHUB_RUN_ATTEMPT': '1',
                               'EXISTING_ASSET': 'lake-native-cache-Linux-X64-fixture-1-1.tar' if asset_exists else '',
                               'REPOSITORY': 'fixture/aglib', 'REVISION': '0123456'},
                capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, status, result.stderr)
            commands = (root / 'trace').read_text().splitlines()
            self.assertEqual(len(commands), 1 if asset_exists else 2)
            self.assertTrue(commands[0].startswith('release view lean-native-0123456 '))
            if asset_exists:
                return
            if exists:
                self.assertEqual(commands[1],
                                 'release upload lean-native-0123456 lake-native-cache-Linux-X64-fixture-1-1.tar --repo fixture/aglib')
            else:
                self.assertTrue(commands[1].startswith(
                    'release create lean-native-0123456 lake-native-cache-Linux-X64-fixture-1-1.tar '))
                self.assertIn('--latest=false', commands[1])
                self.assertIn('--prerelease', commands[1])


class CurrentArtifactTransfer(unittest.TestCase):
    def test_current_run_artifact_and_native_completeness_are_mandatory(self):
        steps = JOBS['test_lint']['steps']
        download = step('test_lint', "Download this run's Build outputs")
        restore = step('test_lint', "Restore this run's native Build outputs")
        verify = step('test_lint', 'Verify Build outputs without compilation')
        self.assertTrue(download['uses'].startswith('actions/download-artifact@'))
        self.assertEqual(download['with'], {'name': 'cache-staging',
                                          'path': '${{ runner.temp }}/lake-native-cache'})
        for item in (download, restore, verify):
            self.assertFalse(item.get('continue-on-error', False))
            self.assertNotIn('if', item)
        self.assertLess(steps.index(download), steps.index(restore))
        self.assertLess(steps.index(restore), steps.index(verify))
        self.assertLess(steps.index(verify), steps.index(step('test_lint', 'Test')))
        self.assertIn('lake cache unstage "$RUNNER_TEMP/cache-staging" --force-overwrite',
                      restore['run'])
        self.assertIn('LAKE_RESTORE_ARTIFACTS=true lake build --no-build --rehash', verify['run'])
        self.assertIn('"${targets[@]}"', verify['run'])
        for target in ('batteries/runLinter', 'mathlib/lint-style', 'mathlib/mk_all', 'CHECK_TARGETS'):
            self.assertNotIn(target, verify['run'])
        for result in ('success', 'failure', 'skipped', 'cancelled'):
            self.assertEqual(condition(step('test_lint', 'Test')['if'], {
                'needs.build.result': 'success', 'steps.compiled.outcome': result,
                'steps.tools.outcome': 'success'}),
                result == 'success')

    def test_warm_cache_cannot_substitute_for_missing_or_invalid_current_archive(self):
        for archive, unstage_status in (('valid', 0), ('missing', 0), ('invalid', 0), ('valid', 1)):
            with self.subTest(archive=archive, unstage_status=unstage_status):
                with tempfile.TemporaryDirectory(prefix='lean-ci-transfer-') as directory:
                    root = Path(directory)
                    cache = root / 'cache'
                    cache.mkdir()
                    (cache / 'warm-output').write_text('historical output exists')
                    if archive == 'valid':
                        mappings = root / 'outputs.jsonl'
                        mappings.write_text('current mappings')
                        with tarfile.open(cache / 'lake-native-cache.tar', 'w') as stream:
                            stream.add(mappings, arcname='outputs.jsonl')
                    elif archive == 'invalid':
                        (cache / 'lake-native-cache.tar').write_text('invalid archive')
                    mock = 'lake() { echo "$*" >> "$TRACE"; return "$UNSTAGE_STATUS"; }\n'
                    result = subprocess.run(
                        ['bash', '-e', '-o', 'pipefail', '-c', mock + step(
                            'test_lint', "Restore this run's native Build outputs")['run']],
                        cwd=root, env={**os.environ, 'RUNNER_TEMP': directory,
                                       'LAKE_CACHE_DIR': str(cache), 'TRACE': directory + '/trace',
                                       'UNSTAGE_STATUS': str(unstage_status)},
                        capture_output=True, text=True, check=False)
                    self.assertEqual(result.returncode == 0, archive == 'valid' and unstage_status == 0)
                    if result.returncode == 0:
                        self.assertFalse((cache / 'lake-native-cache.tar').exists())
                        self.assertEqual((root / 'cache-staging/outputs.jsonl').read_text(),
                                         'current mappings')
                    elif archive != 'valid':
                        self.assertFalse((root / 'trace').exists())


class AuditorReuseAndTargets(unittest.TestCase):
    def test_pinned_auditor_is_prepared_only_in_test_and_reuses_cached_checkout(self):
        audit = step('test_lint', 'Audit production axioms')
        self.assertTrue(audit['continue-on-error'])
        self.assertEqual(audit['working-directory'], '${{ inputs.package-directory }}')
        mock = r"""
git() {
  printf 'git:%s\n' "$*" >> "$TRACE"
  if test "$1" = clone; then mkdir -p "${@: -1}/.git"; return "$CLONE_STATUS"; fi
  printf '%s\n' "$TOOL_REVISION"
}
lake() {
  printf 'lake:%s\n' "$*" >> "$TRACE"
  if test "$1" = build; then
    test "$TOOL_BUILD_STATUS" = 0 || return "$TOOL_BUILD_STATUS"
    mkdir -p .lake/build/bin
    printf '#!/bin/sh\nexit 0\n' > .lake/build/bin/axiom-audit
    chmod +x .lake/build/bin/axiom-audit
  fi
}
"""
        with tempfile.TemporaryDirectory(prefix='lean-ci-auditor-') as directory:
            root = Path(directory)
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            environment = {**os.environ, 'TRACE': directory + '/trace', 'BUILD_TARGETS': 'Aglib',
                           'LAKE_CACHE_DIR': directory + '/cache', 'RUNNER_TEMP': directory, 'CLONE_STATUS': '0',
                           'TOOL_REVISION': '46024e005996495c65ef609368e11ab39c4222e3',
                           'TOOL_BUILD_STATUS': '0'}
            for _ in range(2):
                result = subprocess.run(['bash', '-e', '-o', 'pipefail', '-c', mock + audit['run']],
                                        cwd=root, env=environment, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
            trace = (root / 'trace').read_text().splitlines()
            self.assertEqual(sum(line.startswith('git:clone ') for line in trace), 1)
            self.assertEqual(trace.count('lake:build'), 2)
            self.assertEqual((root / 'cache/axiom-audit/lean-toolchain').read_text(),
                             (root / 'lean-toolchain').read_text())
            for settings in ({'TOOL_REVISION': 'wrong-pin'}, {'TOOL_BUILD_STATUS': '1'},
                             {'LAKE_CACHE_DIR': directory + '/cold-failure', 'CLONE_STATUS': '1'}):
                with self.subTest(settings=settings):
                    result = subprocess.run(
                        ['bash', '-e', '-o', 'pipefail', '-c', mock + audit['run']],
                        cwd=root, env={**environment, **settings}, capture_output=True, text=True)
                    self.assertNotEqual(result.returncode, 0)

    def test_build_only_auditor_cache_acquires_local_source_without_losing_outputs(self):
        with tempfile.TemporaryDirectory(prefix='ci-auditor-build-only-') as directory:
            root = Path(directory)
            source = root / 'source'
            source.mkdir()
            subprocess.run(['git', 'init', '-q', str(source)], check=True)
            (source / 'lakefile.toml').write_text('name = "fixture-auditor"\n')
            (source / 'Main.lean').write_text('-- source fixture\n')
            subprocess.run(['git', '-C', str(source), 'add', 'lakefile.toml', 'Main.lean'], check=True)
            subprocess.run(['git', '-C', str(source), '-c', 'user.name=CI fixture',
                            '-c', 'user.email=ci-fixture@example.invalid', 'commit', '-qm', 'fixture'], check=True)
            subprocess.run(['git', '-C', str(source), 'tag', 'v0.1.2'], check=True)
            revision = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip()
            tool = root / 'cache/axiom-audit'
            binary = tool / '.lake/build/bin/axiom-audit'
            binary.parent.mkdir(parents=True)
            binary.write_text('#!/bin/sh\nexit 0\n'); binary.chmod(0o755)
            completed = tool / '.lake/build/ir/completed.o'
            completed.parent.mkdir(); completed.write_bytes(b'restored native object')
            before = completed.stat()
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            self.assertFalse((tool / '.git').exists())
            command = step('test_lint', 'Audit production axioms')['run']
            self.assertIn('test "$(git -C "$tool" rev-parse HEAD)" = 46024e005996495c65ef609368e11ab39c4222e3', command)
            # Only the fixture's expected commit replaces the production pin in this test.
            command = command.replace('46024e005996495c65ef609368e11ab39c4222e3', revision)
            mock = r'''
git() {
  if test "$1" = clone; then
    command git clone --quiet --depth 1 --branch v0.1.2 "$FIXTURE_SOURCE" "${@: -1}"
  else
    command git "$@"
  fi
}
lake() {
  if test "$1" = build; then
    test -f Main.lean && test -f lakefile.toml
    test "$(cat .lake/build/ir/completed.o)" = 'restored native object'
  elif test "$1" = env; then
    shift; "$@"
  else
    return 99
  fi
}
'''
            result = subprocess.run(['bash', '-eo', 'pipefail', '-c', mock + command], cwd=root,
                                    env={**os.environ, 'RUNNER_TEMP': directory,
                                         'LAKE_CACHE_DIR': str(root / 'cache'), 'BUILD_TARGETS': 'Aglib',
                                         'FIXTURE_SOURCE': source.as_uri()}, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(subprocess.check_output(['git', '-C', str(tool), 'rev-parse', 'HEAD'],
                                                    text=True).strip(), revision)
            self.assertEqual(completed.read_bytes(), b'restored native object')
            self.assertEqual(completed.stat().st_ino, before.st_ino)
            self.assertEqual(completed.stat().st_mtime_ns, before.st_mtime_ns)
            self.assertEqual(binary.stat().st_mode & 0o777, 0o755)
            self.assertEqual((tool / 'lean-toolchain').read_text(), (root / 'lean-toolchain').read_text())
            self.assertEqual(list(root.glob('axiom-audit-source.*')), [])

    def test_build_artifact_contains_only_mathematical_outputs(self):
        upload = next(item for item in JOBS['build']['steps']
                      if item.get('uses', '').startswith('actions/upload-artifact@')
                      and item.get('with', {}).get('name') == 'cache-staging')
        self.assertEqual(upload['with']['path'], '${{ runner.temp }}/lake-native-cache.tar')
        self.assertNotIn('axiom', step('build', 'Stage completed native outputs')['run'])
        self.assertNotIn('axiom', step('test_lint', "Restore this run's native Build outputs")['run'])

    def test_actual_stage_and_restore_need_only_the_math_archive(self):
        with tempfile.TemporaryDirectory(prefix='lean-ci-math-transfer-') as directory:
            root = Path(directory)
            build = root / 'build'
            build.mkdir()
            (build / 'outputs.jsonl').write_text('current native outputs')
            (build / 'lean-toolchain').write_text('fixture\n')
            (build / 'lakefile.toml').write_text('name = \"Fixture\"\n')
            mock = r"""
lean() { printf 'Lean fixture\n'; }
lake() {
  if test "$2" = stage; then
    mkdir -p "$4"
    cp "$3" "$4/outputs.jsonl"
  elif test "$2" = unstage; then
    test -s "$3/outputs.jsonl"
  else
    return 99
  fi
}
"""
            result = subprocess.run(
                ['bash', '-e', '-o', 'pipefail', '-c', mock + step(
                    'build', 'Stage completed native outputs')['run']],
                env={**os.environ, 'RUNNER_TEMP': str(build), 'COPYFILE_DISABLE': '1',
                     'GITHUB_OUTPUT': str(root / 'stage-output'), 'RUNNER_OS': 'Linux', 'RUNNER_ARCH': 'X64',
                     'GITHUB_REPOSITORY': 'fixture/package', 'GITHUB_SHA': '0123456'},
                cwd=build, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((root / 'stage-output').read_text(), 'staged=true\n')
            with tarfile.open(build / 'lake-native-cache.tar') as archive:
                self.assertEqual(set(archive.getnames()), {'.', './outputs.jsonl', './producer.json'})
            test = root / 'test'
            download = test / 'download'
            download.mkdir(parents=True)
            (download / 'lake-native-cache.tar').write_bytes((build / 'lake-native-cache.tar').read_bytes())
            result = subprocess.run(
                ['bash', '-e', '-o', 'pipefail', '-c', mock + step(
                    'test_lint', "Restore this run's native Build outputs")['run']],
                env={**os.environ, 'RUNNER_TEMP': str(test), 'LAKE_CACHE_DIR': str(download)},
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse((download / 'lake-native-cache.tar').exists())
            self.assertEqual((test / 'cache-staging/outputs.jsonl').read_text(), 'current native outputs')

    def test_actual_callers_supply_declared_production_roots_without_changing_release_pins(self):
        # Package directories are sibling checkouts in the integration workspace.
        for name, expected in (('aglib', 'Aglib'), ('quillen-k-theory', 'Quillen'),
                               ('motivic', 'Motivic')):
            root = ROOT.parent / name
            with self.subTest(package=name):
                if not root.exists():
                    self.skipTest('sibling callers require the integration workspace')
                caller = yaml.safe_load((root / '.github/workflows/ci.yml').read_text())['jobs']['lean']
                self.assertEqual(caller['with']['package-directory'], '.')
                self.assertEqual(caller['with']['build-targets'], expected)
                config = tomllib.loads((root / 'lakefile.toml').read_text())
                self.assertIn(expected, [lib['name'] for lib in config['lean_lib']])
                self.assertTrue((root / f'{expected}.lean').is_file())
                if name != 'aglib':
                    self.assertRegex(caller['uses'],
                                     r'\Akangxyz/aglib/\.github/workflows/lean-ci\.yml@[0-9a-f]{40}\Z')

    def test_empty_targets_fail_all_native_entries_before_external_commands(self):
        names = [('test_lint', 'Check generated library entries'), ('test_lint', 'Mathlib text style'),
                 ('build', 'Build'), ('test_lint', 'Verify Build outputs without compilation'),
                 ('test_lint', 'Lint'), ('test_lint', 'Audit production axioms')]
        with tempfile.TemporaryDirectory(prefix='lean-ci-empty-targets-') as directory:
            mock = 'lake() { echo unexpected-call >&2; return 99; }\n'
            for job, name in names:
                for targets in ('', '   ', '\t'):
                    with self.subTest(step=name, targets=targets):
                        result = subprocess.run(
                            ['bash', '-e', '-o', 'pipefail', '-c', mock + step(job, name)['run']],
                            env={**os.environ, 'BUILD_TARGETS': targets, 'RUNNER_TEMP': directory},
                            capture_output=True, text=True)
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn('at least one production root', result.stdout)
                        self.assertNotIn('unexpected-call', result.stderr)

    def test_production_audit_visits_every_root_and_propagates_failure(self):
        with tempfile.TemporaryDirectory(prefix='lean-ci-audit-roots-') as directory:
            root = Path(directory)
            tool = root / 'cache/axiom-audit'
            (tool / '.git').mkdir(parents=True)
            binary = tool / '.lake/build/bin/axiom-audit'
            binary.parent.mkdir(parents=True)
            binary.write_text('#!/bin/sh\nexit 0\n')
            binary.chmod(0o755)
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            mock = r"""
git() { printf '%s\n' 46024e005996495c65ef609368e11ab39c4222e3; }
lake() {
  printf '%s\n' "$*" >> "$TRACE"
  test "$1" = build || test "${@: -1}" != "$FAIL_ROOT"
}
"""
            for failure in ('none', 'Aglib', 'Quillen'):
                trace = root / 'trace'
                trace.write_text('')
                result = subprocess.run(
                    ['bash', '-e', '-o', 'pipefail', '-c', mock + step(
                        'test_lint', 'Audit production axioms')['run']], cwd=root,
                    env={**os.environ, 'LAKE_CACHE_DIR': str(root / 'cache'),
                         'BUILD_TARGETS': 'Aglib Quillen', 'TRACE': str(trace), 'FAIL_ROOT': failure},
                    capture_output=True, text=True)
                self.assertEqual(result.returncode, 0 if failure == 'none' else 1, result.stderr)
                self.assertEqual(trace.read_text().splitlines(), [
                    'build', f'env {binary} --root Aglib', f'env {binary} --root Quillen'])


class NativeSetup(unittest.TestCase):
    def run_setup(self, **settings):
        """Run the actual workflow shell, replacing only external commands."""
        with tempfile.TemporaryDirectory(prefix='lean-ci-setup-') as directory:
            root = Path(directory)
            binary = root / 'bin'
            binary.mkdir()
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            installer = root / 'installer'
            installer.write_text('#!/bin/sh\nprintf "installer:%s\\n" "$*" >> "$TRACE"\n'
                                 'exit "${INSTALLER_STATUS:-0}"\n')
            curl = binary / 'curl'
            curl.write_text('''#!/bin/sh
printf 'curl:%s\\n' "$*" >> "$TRACE"
test "${CURL_STATUS:-0}" -eq 0 || exit "$CURL_STATUS"
while test "$#" -gt 0; do
  if test "$1" = --output; then cp "$FIXTURE_INSTALLER" "$2"; exit 0; fi
  shift
done
exit 2
''')
            lake = binary / 'fixture-lake'
            lake.write_text('#!/bin/sh\nprintf "lake:%s\\n" "$*" >> "$TRACE"\n'
                            'exit "${LAKE_STATUS:-0}"\n')
            curl.chmod(0o755)
            lake.chmod(0o755)
            # Shell functions also override commands after setup prepends Elan's
            # real bin directory. No change to HOME or any installed toolchain.
            mocks = r'''
elan() {
  printf 'elan:%s:toolchain=%s\n' "$*" "$(cat lean-toolchain)" >> "$TRACE"
  count=$(cat "$ATTEMPTS" 2>/dev/null || echo 0)
  count=$((count + 1))
  echo "$count" > "$ATTEMPTS"
  test "$count" -gt "${FAIL_ATTEMPTS:-0}" || return 35
  printf '%s\n' "$FIXTURE_LAKE"
}
lean() { printf 'lean:%s\n' "$*" >> "$TRACE"; return "${LEAN_STATUS:-0}"; }
sleep() { printf 'sleep:%s\n' "$*" >> "$TRACE"; }
'''
            environment = {**os.environ, 'PATH': str(binary) + os.pathsep + os.environ['PATH'],
                           'RUNNER_TEMP': directory, 'GITHUB_PATH': directory + '/github-path',
                           'TRACE': directory + '/trace', 'ATTEMPTS': directory + '/attempts',
                           'FIXTURE_INSTALLER': str(installer), 'FIXTURE_LAKE': str(lake),
                           **{key: str(value) for key, value in settings.items()}}
            result = subprocess.run(
                ['bash', '-e', '-o', 'pipefail', '-c', mocks + step('build', 'Configure Lean')['run']],
                cwd=root, env=environment, capture_output=True, text=True, timeout=5, check=False)
            return result, (root / 'trace').read_text()

    def test_both_jobs_use_same_self_contained_mathlib_setup(self):
        setup = step('build', 'Configure Lean')
        self.assertEqual(setup, step('test_lint', 'Configure Lean'))
        self.assertNotIn('uses', setup)
        self.assertFalse(setup.get('continue-on-error', False))
        self.assertEqual(setup['working-directory'], '${{ inputs.package-directory }}')
        self.assertIn('https://elan.lean-lang.org/elan-init.sh', setup['run'])
        self.assertIn('--retry 2 --retry-all-errors', setup['run'])
        self.assertIn('elan which lake', setup['run'])

    def test_success_validates_both_versions_and_selected_toolchain(self):
        result, trace = self.run_setup()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('installer:-y --default-toolchain none', trace)
        self.assertIn('elan:which lake:toolchain=leanprover/lean4:v4.34.1', trace)
        self.assertIn('lean:--version', trace)
        self.assertIn('lake:--version', trace)
        self.assertNotIn('sleep:', trace)

    def test_transient_toolchain_failure_recovers_on_third_attempt(self):
        result, trace = self.run_setup(FAIL_ATTEMPTS=2)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(trace.count('elan:which lake:'), 3)
        self.assertEqual(trace.count('sleep:'), 2)
        self.assertIn('lake:--version', trace)

    def test_permanent_toolchain_failure_is_fatal_after_three_attempts(self):
        result, trace = self.run_setup(FAIL_ATTEMPTS=9)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(trace.count('elan:which lake:'), 3)
        self.assertEqual(trace.count('sleep:'), 2)
        self.assertNotIn('lean:--version', trace)
        self.assertIn('failed after 3 attempts', result.stdout)

    def test_installer_download_or_execution_failure_is_fatal(self):
        for settings in ({'CURL_STATUS': 22}, {'INSTALLER_STATUS': 1}):
            with self.subTest(settings=settings):
                result, trace = self.run_setup(**settings)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn('elan:', trace)

    def test_failed_version_validation_is_fatal(self):
        for settings in ({'LEAN_STATUS': 1}, {'LAKE_STATUS': 1}):
            with self.subTest(settings=settings):
                result, trace = self.run_setup(**settings)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(trace.count('elan:which lake:'), 1)


class LayeredCacheIntegration(unittest.TestCase):
    def test_capability_detection_requires_both_helpers_and_preserves_legacy_and_promotion(self):
        select = step('build', 'Select layered cache support')
        self.assertEqual(select, step('test_lint', 'Select layered cache support'))
        with tempfile.TemporaryDirectory(prefix='ci-cache-capability-') as directory:
            root = Path(directory)
            helper = root / '.github/ci-cache/checkpoint.py'
            for available, stage_available, promotion, expected in (
                    (False, False, '', False), (True, True, 'sealed', False),
                    (True, False, '', False), (True, True, '', True)):
                if available:
                    helper.parent.mkdir(parents=True, exist_ok=True)
                    helper.write_text('import os\nwith open(os.environ["GITHUB_OUTPUT"], "a") as f: '
                                      'f.write("root_context=fixture\\n")\n')
                stage_helper = helper.with_name('stage.py')
                if stage_available:
                    stage_helper.write_text('# stage capability fixture\n')
                else:
                    stage_helper.unlink(missing_ok=True)
                output = root / 'output'; output.write_text('')
                result = subprocess.run(['bash', '-eo', 'pipefail', '-c', select['run']], cwd=root,
                                        env={**os.environ, 'FIRST_CI_CACHE': promotion,
                                             'GITHUB_OUTPUT': str(output)}, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual('layered=true' in output.read_text(), expected)
                self.assertEqual('root_context=fixture' in output.read_text(), expected)

    def test_actual_supported_preflight_routes_overrides_and_external_paths_to_legacy(self):
        select = step('build', 'Select layered cache support')
        with tempfile.TemporaryDirectory(prefix='ci-supported-mode-') as directory:
            for kind, expected in (('standard', True), ('overrides', False),
                                   ('external-path', False), ('custom-layout', False)):
                root = Path(directory) / kind
                helper = root / '.github/ci-cache/checkpoint.py'
                helper.parent.mkdir(parents=True)
                shutil.copyfile(ROOT / '.github/ci-cache/checkpoint.py', helper)
                helper.with_name('stage.py').write_text('# stage capability fixture\n')
                (root / 'lakefile.toml').write_text('name = "Fixture"\n')
                (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
                manifest = {'packagesDir': '.lake/packages', 'packages': []}
                if kind == 'external-path':
                    manifest['packages'] = [{'name': 'External', 'type': 'path',
                                             'dir': str(Path(directory) / 'outside-fixture')}]
                if kind == 'custom-layout':
                    manifest['packagesDir'] = 'custom-packages'
                if kind == 'overrides':
                    override = root / '.lake/package-overrides.json'
                    override.parent.mkdir()
                    override.write_text('{}\n')
                (root / 'lake-manifest.json').write_text(json.dumps(manifest))
                output = root / 'outputs'
                output.write_text('')
                result = subprocess.run(['bash', '-eo', 'pipefail', '-c', select['run']], cwd=root,
                                        env={**os.environ, 'FIRST_CI_CACHE': '', 'GITHUB_OUTPUT': str(output)},
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, (kind, result.stderr))
                self.assertEqual('layered=true' in output.read_text(), expected, kind)
                self.assertEqual('root_context=' in output.read_text(), expected, kind)
                if not expected:
                    self.assertIn('Checkpoint failed:', result.stderr)

    def test_migration_introduced_override_fails_support_check_before_native_work(self):
        revalidate = step('build', 'Revalidate layered support after migration restore')
        self.assertFalse(revalidate.get('continue-on-error', False))
        self.assertTrue(condition(revalidate['if'], {'steps.cache-mode.outputs.layered': 'true'}))
        self.assertFalse(condition(revalidate['if'], {'steps.cache-mode.outputs.layered': ''}))
        steps = JOBS['build']['steps']
        old_restore = next(action for action in steps if action.get('id') == 'restore')
        self.assertLess(steps.index(old_restore), steps.index(revalidate))
        for name in ('Remove read-only restored archive hash sidecars', 'Configure Lean', 'Get Mathlib cache',
                     'Apply optional compilation checkpoints', 'Build'):
            self.assertLess(steps.index(revalidate), steps.index(step('build', name)))
        with tempfile.TemporaryDirectory(prefix='ci-migration-override-') as directory:
            root = Path(directory)
            helper = root / '.github/ci-cache/checkpoint.py'
            helper.parent.mkdir(parents=True)
            shutil.copyfile(ROOT / '.github/ci-cache/checkpoint.py', helper)
            (root / 'lakefile.toml').write_text('name = "Fixture"\n')
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            (root / 'lake-manifest.json').write_text('{"packages": []}\n')
            before = subprocess.run(['bash', '-eo', 'pipefail', '-c', revalidate['run']], cwd=root,
                                    capture_output=True, text=True)
            self.assertEqual(before.returncode, 0, before.stderr)
            override = root / '.lake/package-overrides.json'
            override.parent.mkdir(); override.write_text('{}\n')
            after = subprocess.run(['bash', '-eo', 'pipefail', '-c', revalidate['run']], cwd=root,
                                   capture_output=True, text=True)
            self.assertNotEqual(after.returncode, 0)
            self.assertIn('package-overrides.json', after.stderr)

    def test_materialized_guards_follow_acquisition_and_precede_checkpoint_overlays(self):
        for job, previous, following in (
                ('build', 'Restore published native dependency caches', 'Apply optional compilation checkpoints'),
                ('test_lint', 'Fetch pinned dependency sources without compilation', 'Apply optional Test and tool checkpoints')):
            actions = JOBS[job]['steps']
            guard = step(job, 'Validate materialized layered dependencies')
            self.assertEqual(guard['run'], 'python3 .github/ci-cache/checkpoint.py supported --root . --materialized')
            self.assertFalse(guard.get('continue-on-error', False))
            self.assertTrue(condition(guard['if'], {'steps.cache-mode.outputs.layered': 'true'}))
            self.assertFalse(condition(guard['if'], {'steps.cache-mode.outputs.layered': ''}))
            self.assertLess(actions.index(step(job, previous)), actions.index(guard))
            self.assertLess(actions.index(guard), actions.index(step(job, following)))
            if job == 'build':
                self.assertLess(actions.index(step(job, 'Get Mathlib cache')), actions.index(guard))
                self.assertLess(actions.index(guard), actions.index(step(job, 'Build')))
            else:
                self.assertLess(actions.index(guard), actions.index(step(job, "Overlay this run's complete dependency closure")))
                self.assertLess(actions.index(guard), actions.index(step(job, 'Verify Build outputs without compilation')))

    def test_materialized_guard_rejects_missing_custom_and_drifted_dependency_configs(self):
        command = step('build', 'Validate materialized layered dependencies')['run']
        with tempfile.TemporaryDirectory(prefix='ci-materialized-config-') as directory:
            root = Path(directory)
            helper = root / '.github/ci-cache/checkpoint.py'
            helper.parent.mkdir(parents=True)
            shutil.copyfile(ROOT / '.github/ci-cache/checkpoint.py', helper)
            (root / 'lakefile.toml').write_text('name = "Fixture"\n')
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            manifest = root / 'lake-manifest.json'
            manifest.write_text(json.dumps({'packages': [{'name': 'dependency', 'type': 'git',
                                                         'url': 'https://example.invalid/dependency',
                                                         'rev': 'a' * 40}]}))
            def run(value):
                return subprocess.run(['bash', '-eo', 'pipefail', '-c', value], cwd=root,
                                      capture_output=True, text=True)
            # Initial static selection can happen before source checkouts exist.
            self.assertEqual(run('python3 .github/ci-cache/checkpoint.py supported --root .').returncode, 0)
            missing = run(command)
            self.assertNotEqual(missing.returncode, 0)
            self.assertIn('not materialized', missing.stderr)
            config = root / '.lake/packages/dependency/lakefile.toml'
            config.parent.mkdir(parents=True)
            config.write_text('name = "dependency"\n')
            self.assertEqual(run(command).returncode, 0)
            config.write_text('name = "dependency"\nbuildDir = "custom-build"\n')
            custom = run(command)
            self.assertNotEqual(custom.returncode, 0)
            self.assertIn('custom generated build directory', custom.stderr)
            manifest.write_text(json.dumps({'packages': [{'name': 'mathlib', 'type': 'git',
                'url': 'https://github.com/leanprover-community/mathlib4',
                'rev': 'd13f23b723b8a846827a245b89c10fc7d3f11612', 'configFile': 'lakefile.lean'}]}))
            self.assertEqual(run('python3 .github/ci-cache/checkpoint.py supported --root .').returncode, 0)
            known = root / '.lake/packages/mathlib/lakefile.lean'
            known.parent.mkdir(parents=True); known.write_text('-- drifted known executable configuration\n')
            drift = run(command)
            self.assertNotEqual(drift.returncode, 0)
            self.assertIn('known dependency configuration bytes changed', drift.stderr)

    def test_old_full_caches_are_only_read_only_migration_fallback(self):
        restore = next(item for item in JOBS['build']['steps'] if item.get('id') == 'restore')
        for layered in ('', 'true'):
            for missing in (False, True):
                for failed in (False, True):
                    values = {'steps.cache-mode.outputs.layered': layered,
                              'steps.restore-dependencies.outcome': 'failure' if failed else 'success',
                              'steps.restore-root.outcome': 'success',
                              'steps.restore-dependencies.outputs.cache-matched-key': '' if missing else 'dep',
                              'steps.restore-root.outputs.cache-matched-key': 'root'}
                    self.assertEqual(condition(restore['if'], values), layered != 'true' or missing or failed)
        for job, name in (('build', 'Save compilation independently of Test and lint'),
                          ('test_lint', 'Save completed Test compilation')):
            self.assertFalse(condition(step(job, name)['if'], {
                'steps.cache-mode.outputs.layered': 'true', 'steps.quiesce.outcome': 'success'},
                success=False, cancelled=True))
        warm = step('test_lint', 'Warm dependency and native compilation outputs')
        self.assertFalse(condition(warm['if'], {'steps.cache-mode.outputs.layered': 'true'}))

    def test_layered_dependency_transport_is_mandatory_even_for_warm_no_change_build(self):
        for name in ("Download this run's dependencies on cache miss",
                     "Restore this run's dependencies on cache miss"):
            action = step('test_lint', name)
            for status, key in (('success', 'old-but-warm'), ('success', ''), ('failure', 'partial')):
                self.assertTrue(condition(action['if'], {
                    'steps.cache-mode.outputs.layered': 'true', 'steps.restore-cache.outcome': status,
                    'steps.restore-cache.outputs.cache-matched-key': key}))
                self.assertFalse(action.get('continue-on-error', False))
        with tempfile.TemporaryDirectory(prefix='ci-layered-handoff-') as directory:
            root = Path(directory)
            archive = root / 'layered-cache/dependencies.tar.zst'
            archive.parent.mkdir()
            archive.write_bytes(b'complete previously restored unpublished dependency, zero new compilation')
            environment = {**os.environ, 'RUNNER_TEMP': directory, 'LAYERED_CACHE': 'true'}
            stage = subprocess.run(['bash', '-eo', 'pipefail', '-c', step(
                'build', 'Stage native dependencies for Test')['run']], env=environment,
                capture_output=True, text=True)
            self.assertEqual(stage.returncode, 0, stage.stderr)
            transfer = root / 'build-dependencies.tar.zst'
            self.assertEqual(archive.stat().st_ino, transfer.stat().st_ino)
            download = root / 'build-dependencies'; download.mkdir()
            transfer.rename(download / transfer.name)
            restored = subprocess.run(['bash', '-eo', 'pipefail', '-c', step(
                'test_lint', "Restore this run's dependencies on cache miss")['run']],
                env={**environment, 'LAKE_CACHE_DIR': str(root / 'native')}, capture_output=True, text=True)
            self.assertEqual(restored.returncode, 0, restored.stderr)
            self.assertEqual((root / 'current-dependencies.tar.zst').read_bytes(), archive.read_bytes())
            self.assertFalse(download.exists())

    def test_layered_test_fetches_sources_without_building_the_mathlib_cache_tool(self):
        source = step('test_lint', 'Fetch pinned dependency sources without compilation')
        self.assertEqual(source['run'], 'lake env true')
        for layered in ('', 'true'):
            values = {'steps.cache-mode.outputs.layered': layered,
                      'steps.restore-cache.outcome': 'failure',
                      'steps.restore-cache.outputs.cache-matched-key': ''}
            self.assertEqual(condition(source['if'], values), layered == 'true')
            self.assertEqual(condition(step('test_lint', 'Recover Mathlib dependencies on cache miss')['if'],
                                       values), layered != 'true')
        steps = JOBS['test_lint']['steps']
        self.assertLess(steps.index(source), steps.index(step('test_lint', 'Apply optional Test and tool checkpoints')))

    def test_optional_restores_and_public_seeds_precede_authoritative_overlays(self):
        steps = JOBS['test_lint']['steps']
        current_dep = step('test_lint', "Overlay this run's complete dependency closure")
        current_root = step('test_lint', "Restore this run's native Build outputs")
        verify = step('test_lint', 'Verify Build outputs without compilation')
        for name in ('Apply optional Test and tool checkpoints', 'Recover Mathlib dependencies on cache miss',
                     'Fetch pinned dependency sources without compilation'):
            self.assertLess(steps.index(step('test_lint', name)), steps.index(current_dep))
        for action in steps:
            if action.get('uses', '').startswith('actions/cache/restore@'):
                self.assertLess(steps.index(action), steps.index(current_dep))
        self.assertLess(steps.index(current_dep), steps.index(current_root))
        self.assertLess(steps.index(current_root), steps.index(verify))
        self.assertIn('--layer dependencies', current_dep['run'])
        self.assertFalse(current_dep.get('continue-on-error', False))
        self.assertIn('--no-build --rehash', verify['run'])
        # No old cache may overwrite verified production files later in Test.
        for action in steps[steps.index(current_root) + 1:]:
            self.assertNotIn('checkpoint.py restore', action.get('run', ''))
            self.assertFalse(action.get('uses', '').startswith('actions/cache/restore@'))

    def test_bad_optional_checkpoint_does_not_prevent_current_authoritative_restore(self):
        with tempfile.TemporaryDirectory(prefix='ci-layered-optional-') as directory:
            root = Path(directory)
            for layer in ('root', 'tools'):
                archive = root / f'layered-cache/{layer}.tar.zst'
                archive.parent.mkdir(exist_ok=True)
                archive.write_text('optional invalid archive')
            mock = 'python3() { printf "%s\\n" "$*" >> "$TRACE"; return 17; }\n'
            result = subprocess.run(['bash', '-eo', 'pipefail', '-c', mock + step(
                'test_lint', 'Apply optional Test and tool checkpoints')['run']], cwd=root,
                env={**os.environ, 'RUNNER_TEMP': directory, 'LAKE_CACHE_DIR': str(root / 'native'),
                     'TRACE': str(root / 'trace')}, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            calls = (root / 'trace').read_text().splitlines()
            self.assertEqual(len(calls), 2)
            self.assertIn('--layer root', calls[0])
            self.assertIn('--layer tools', calls[1])
            self.assertEqual(result.stdout.count('::warning::'), 2)

    def test_both_partial_layers_save_after_failure_or_timeout_without_publication(self):
        actions = JOBS['build']['steps']
        quiesce = step('build', "Quiesce this job's native scopes before cache saving")
        for layer in ('root', 'dependencies'):
            pack = step('build', f'Pack completed {layer} checkpoint')
            save = step('build', f'Save completed {layer} checkpoint')
            self.assertEqual(pack['shell'], 'bash')
            self.assertLess(actions.index(quiesce), actions.index(pack))
            self.assertLess(actions.index(pack), actions.index(save))
            for outcome in ('success', 'failure', 'skipped', 'cancelled'):
                values = {'steps.cache-mode.outputs.layered': 'true', 'steps.quiesce.outcome': outcome,
                          'steps.build.outcome': 'failure', 'steps.staging-quiesce.outcome': 'success'}
                self.assertEqual(condition(pack['if'], values, success=False, cancelled=True), outcome == 'success')
            values = {'steps.quiesce.outcome': 'success', 'steps.build.outcome': 'failure', 'steps.staging-quiesce.outcome': 'success',
                      f'steps.pack-{layer}.outcome': 'success',
                      'steps.pack-dependencies.outputs.changed': 'true',
                      'steps.restore-dependencies.outputs.cache-matched-key': ''}
            self.assertTrue(condition(save['if'], values, success=False, cancelled=True))
            self.assertNotIn('/.lake', save['with']['path'])
            self.assertNotIn('lake-native-cache', save['with']['path'])
        for build in ('failure', 'cancelled', 'skipped'):
            self.assertFalse(publish(build=build))
        self.assertIn('rm -f "$RUNNER_TEMP/outputs.jsonl"', step('build', 'Build')['run'])

    def test_dependency_baselines_use_content_generations_and_save_only_changes_or_miss(self):
        save = step('build', 'Save completed dependencies checkpoint')
        self.assertIn('outputs.generation', save['with']['key'])
        self.assertNotIn('github.sha', save['with']['key'])
        for changed in ('true', 'false'):
            for matched in ('', 'immutable-prior-generation'):
                values = {'steps.quiesce.outcome': 'success', 'steps.build.outcome': 'failure', 'steps.staging-quiesce.outcome': 'success',
                          'steps.pack-dependencies.outcome': 'success',
                          'steps.pack-dependencies.outputs.changed': changed,
                          'steps.restore-dependencies.outputs.cache-matched-key': matched}
                self.assertEqual(condition(save['if'], values, success=False), changed == 'true' or matched == '')
        self.assertNotIn('Pack completed dependencies checkpoint',
                         [action.get('name') for action in JOBS['test_lint']['steps']])

    def test_root_and_tool_generations_include_attempt_and_context_without_cross_job_collision(self):
        build_root = step('build', 'Save completed root checkpoint')['with']['key']
        test_root = step('test_lint', 'Save completed root checkpoint')['with']['key']
        self.assertNotEqual(build_root, test_root)
        for job, layer in (('build', 'root'), ('test_lint', 'root'), ('test_lint', 'tools')):
            save = step(job, f'Save completed {layer} checkpoint')
            key = save['with']['key']
            for context in ('github.ref', 'github.run_id', 'github.run_attempt', f'{layer}_context'):
                self.assertIn(context, key)
            self.assertIn('always()', save['if'])
            pack = step(job, f'Pack completed {layer} checkpoint')
            self.assertLess(JOBS[job]['steps'].index(step(job, "Quiesce this job's native scopes before cache saving")),
                            JOBS[job]['steps'].index(pack))
        tools = step('test_lint', 'Pack completed tools checkpoint')['run']
        self.assertIn('--layer tools', tools)
        self.assertNotIn('lake build', tools)
        self.assertNotIn('lake lint', tools)

    def test_root_and_tool_restore_prefer_current_branch_then_compatible_default_seed(self):
        for job, layer in (('build', 'root'), ('test_lint', 'root'), ('test_lint', 'tools')):
            restore = step(job, f'Restore optional {layer} checkpoint')['with']
            prefixes = restore['restore-keys'].splitlines()
            symbolic_context = '${{ steps.cache-mode.outputs.' + layer + '_context }}'
            self.assertEqual(prefixes, [f'lean-layered-v1-{layer}-{symbolic_context}-${{{{ github.ref }}}}-',
                                        f'lean-layered-v1-{layer}-{symbolic_context}-'])
            prefixes = [prefix.replace(symbolic_context, 'compatible-context').replace(
                '${{ github.ref }}', 'refs/heads/new-topic') for prefix in prefixes]
            current = f'lean-layered-v1-{layer}-compatible-context-refs/heads/new-topic-old-run-1'
            default = f'lean-layered-v1-{layer}-compatible-context-refs/heads/main-newer-run-1'
            incompatible = f'lean-layered-v1-{layer}-different-manifest-refs/heads/main-newest-run-1'
            # Candidate visibility is supplied by GitHub; prefix order chooses within it.
            for visible, expected in (([default, current], current), ([default], default),
                                      ([incompatible, default], default), ([incompatible], None)):
                selected = next((key for prefix in prefixes for key in visible if key.startswith(prefix)), None)
                self.assertEqual(selected, expected)

    def test_unchanged_matched_tool_checkpoint_skips_upload_but_progress_keeps_fresh_key(self):
        save = step('test_lint', 'Save completed tools checkpoint')
        for changed in ('true', 'false'):
            for matched in ('', 'existing-tool-generation'):
                for quiesce in ('success', 'failure'):
                    for packed in ('success', 'failure'):
                        values = {'steps.quiesce.outcome': quiesce, 'steps.compiled.outcome': 'success',
                                  'steps.pack-tools.outcome': packed,
                                  'steps.pack-tools.outputs.changed': changed,
                                  'steps.restore-tools.outputs.cache-matched-key': matched}
                        expected = quiesce == 'success' and packed == 'success' and (changed == 'true' or matched == '')
                        self.assertEqual(condition(save['if'], values, success=False, cancelled=True), expected)
        for field in ('github.run_id', 'github.run_attempt'):
            self.assertIn(field, save['with']['key'])

    def test_checkpoint_admission_requires_real_build_attempt_or_verified_test_basis(self):
        for job, layers in (('build', ('root', 'dependencies')), ('test_lint', ('root', 'tools'))):
            for state in ('success', 'failure', 'skipped', 'cancelled', ''):
                values = {'steps.cache-mode.outputs.layered': 'true', 'steps.quiesce.outcome': 'success',
                          'steps.build.outcome': state, 'steps.compiled.outcome': state,
                          'steps.staging-quiesce.outcome': 'success',
                          'steps.pack-root.outcome': 'success', 'steps.pack-dependencies.outcome': 'success',
                          'steps.pack-tools.outcome': 'success', 'steps.pack-dependencies.outputs.changed': 'true',
                          'steps.pack-tools.outputs.changed': 'true',
                          'steps.restore-dependencies.outputs.cache-matched-key': 'prior-useful-generation',
                          'steps.restore-tools.outputs.cache-matched-key': 'prior-useful-generation'}
                expected = state in ('success', 'failure') if job == 'build' else state == 'success'
                for layer in layers:
                    for verb in ('Pack', 'Save'):
                        action = step(job, f'{verb} completed {layer} checkpoint')
                        self.assertEqual(condition(action['if'], values, success=False, cancelled=True), expected,
                                         (job, layer, verb, state))

    def test_pre_overlay_failure_neither_overwrites_downloaded_archive_nor_saves_empty_generation(self):
        with tempfile.TemporaryDirectory(prefix='ci-checkpoint-admission-') as directory:
            root = Path(directory)
            helper = root / '.github/ci-cache/checkpoint.py'
            helper.parent.mkdir(parents=True)
            # Model packing an early, config-only workspace if an admission guard fails.
            helper.write_text('import pathlib, sys\n'
                              'pathlib.Path(sys.argv[sys.argv.index("--output")+1]).write_bytes(b"empty config-only state")\n'
                              'pathlib.Path("packer-ran").touch()\n')
            for job, layers, state in (('build', ('root', 'dependencies'), 'skipped'),
                                       ('test_lint', ('root', 'tools'), 'skipped'),
                                       ('test_lint', ('root', 'tools'), 'failure')):
                values = {'steps.cache-mode.outputs.layered': 'true', 'steps.quiesce.outcome': 'success',
                          'steps.build.outcome': state, 'steps.compiled.outcome': state,
                          'steps.staging-quiesce.outcome': 'success',
                          'steps.pack-dependencies.outputs.changed': 'true', 'steps.pack-tools.outputs.changed': 'true',
                          'steps.restore-dependencies.outputs.cache-matched-key': 'downloaded-dependencies',
                          'steps.restore-tools.outputs.cache-matched-key': 'downloaded-tools'}
                saved = []
                for layer in layers:
                    archive = root / f'layered-cache/{layer}.tar.zst'
                    archive.parent.mkdir(exist_ok=True)
                    archive.write_bytes(b'useful completed compilation from prior run')
                    pack = step(job, f'Pack completed {layer} checkpoint')
                    if condition(pack['if'], values, success=False):
                        result = subprocess.run(['bash', '-eo', 'pipefail', '-c', pack['run']], cwd=root,
                                                env={**os.environ, 'RUNNER_TEMP': directory,
                                                     'LAKE_CACHE_DIR': str(root / 'native'),
                                                     'GITHUB_OUTPUT': str(root / 'output')},
                                                capture_output=True, text=True)
                        self.assertEqual(result.returncode, 0, result.stderr)
                        values[f'steps.pack-{layer}.outcome'] = 'success'
                    else:
                        values[f'steps.pack-{layer}.outcome'] = 'skipped'
                    save = step(job, f'Save completed {layer} checkpoint')
                    if condition(save['if'], values, success=False):
                        saved.append(layer)
                    self.assertEqual(archive.read_bytes(), b'useful completed compilation from prior run')
                self.assertEqual(saved, [])
                self.assertFalse((root / 'packer-ran').exists())

    def test_all_layer_archives_have_context_scoped_prefixes_and_no_broad_paths(self):
        for job in ('build', 'test_lint'):
            for action in JOBS[job]['steps']:
                if not action.get('name', '').startswith('Restore optional '):
                    continue
                self.assertTrue(action['continue-on-error'])
                self.assertIn('_context', action['with']['key'])
                self.assertIn('_context', action['with']['restore-keys'])
                self.assertTrue(action['with']['path'].endswith('.tar.zst'))
                self.assertNotIn('/.lake', action['with']['path'])
                self.assertNotIn('lake-native-cache', action['with']['path'])


class NativeStageValidationIntegration(unittest.TestCase):
    def test_repaired_stage_precedes_checkpoints_and_both_scope_stops_are_required(self):
        actions = JOBS['build']['steps']
        stage = step('build', 'Stage completed native outputs')
        self.assertFalse(stage.get('continue-on-error', False))
        original_stop = step('build', "Quiesce this job's native scopes before cache saving")
        stage_stop = step('build', 'Quiesce native staging before checkpoints')
        self.assertEqual(stage_stop['run'], original_stop['run'])
        self.assertEqual(stage_stop['shell'], 'bash')
        self.assertTrue(condition(stage_stop['if'], {'steps.cache-mode.outputs.layered': 'true'},
                                  success=False, cancelled=True))
        self.assertFalse(condition(stage_stop['if'], {'steps.cache-mode.outputs.layered': ''}, success=False))
        self.assertLess(actions.index(original_stop), actions.index(stage))
        self.assertLess(actions.index(stage), actions.index(stage_stop))
        for layer in ('root', 'dependencies'):
            for verb in ('Pack', 'Save'):
                action = step('build', f'{verb} completed {layer} checkpoint')
                self.assertLess(actions.index(stage_stop), actions.index(action))
                for first_stop in ('success', 'failure'):
                    for second_stop in ('success', 'failure'):
                        values = {'steps.cache-mode.outputs.layered': 'true', 'steps.build.outcome': 'failure',
                                  'steps.quiesce.outcome': first_stop, 'steps.staging-quiesce.outcome': second_stop,
                                  f'steps.pack-{layer}.outcome': 'success',
                                  'steps.pack-dependencies.outputs.changed': 'true',
                                  'steps.restore-dependencies.outputs.cache-matched-key': 'older-generation',
                                  'steps.stage.outcome': 'failure'}
                        self.assertEqual(condition(action['if'], values, success=False, cancelled=True),
                                         first_stop == second_stop == 'success')
        self.assertNotIn('--build ', stage['run'])
        self.assertNotIn('lake build', stage['run'])

    def test_stage_diagnostics_upload_is_always_layered_and_does_not_gate_acceptance(self):
        actions = JOBS['build']['steps']
        upload = step('build', 'Upload native staging diagnostics')
        self.assertTrue(upload['uses'].startswith('actions/upload-artifact@'))
        self.assertTrue(upload['continue-on-error'])
        self.assertEqual(upload['with'], {'name': 'native-stage-validation', 'overwrite': True,
            'path': '${{ runner.temp }}/native-stage-validation.json', 'if-no-files-found': 'ignore',
            'compression-level': 0, 'retention-days': 7})
        self.assertTrue(condition(upload['if'], {'steps.cache-mode.outputs.layered': 'true'},
                                  success=False, cancelled=True))
        self.assertFalse(condition(upload['if'], {'steps.cache-mode.outputs.layered': ''}, success=False))
        self.assertLess(actions.index(step('build', 'Quiesce native staging before checkpoints')), actions.index(upload))
        self.assertLess(actions.index(upload), actions.index(step('build', 'Pack completed root checkpoint')))

    def test_stage_helper_failure_blocks_handoff_and_success_packages_only_validated_stage(self):
        for status in (0, 17):
            with self.subTest(status=status), tempfile.TemporaryDirectory(prefix='ci-stage-validate-') as directory:
                root = Path(directory)
                helper = root / '.github/ci-cache/stage.py'
                helper.parent.mkdir(parents=True)
                helper.write_text('import json, os, pathlib, shutil, sys\n' +
                    'pathlib.Path(os.environ["TRACE"]).write_text(json.dumps(sys.argv[1:]))\n'
                    'stage=pathlib.Path(sys.argv[sys.argv.index("--staging")+1])\n'
                    'stage.mkdir()\n'
                    'shutil.copyfile(sys.argv[sys.argv.index("--mapping")+1],stage/"outputs.jsonl")\n'
                    'pathlib.Path("repaired-working-archive").write_text("repaired derived archive")\n'
                    'sys.exit(int(os.environ["PREPARE_STATUS"]))\n')
                (root / 'outputs.jsonl').write_text('fresh successful root mappings')
                (root / 'lean-toolchain').write_text('fixture\n')
                (root / 'lakefile.toml').write_text('name = "Fixture"\n')
                mock = 'lean() { printf "Lean fixture\\n"; }\nlake() { echo unexpected-direct-stage >&2; return 99; }\n'
                result = subprocess.run(['bash', '-eo', 'pipefail', '-c', mock + step(
                    'build', 'Stage completed native outputs')['run']], cwd=root,
                    env={**os.environ, 'RUNNER_TEMP': directory, 'LAKE_CACHE_DIR': str(root / 'native'),
                         'LAYERED_CACHE': 'true', 'BUILD_TARGETS': 'Aglib Essays', 'FIRST_CI_CACHE': '',
                         'TRACE': str(root / 'trace'), 'PREPARE_STATUS': str(status),
                         'GITHUB_OUTPUT': str(root / 'outputs'), 'RUNNER_OS': 'Linux', 'RUNNER_ARCH': 'X64',
                         'GITHUB_REPOSITORY': 'fixture/project', 'GITHUB_SHA': '0123456'},
                    capture_output=True, text=True)
                self.assertEqual(result.returncode, status, result.stderr)
                argv = json.loads((root / 'trace').read_text())
                self.assertEqual(argv[0], 'prepare')
                self.assertEqual([argv[index + 1] for index, arg in enumerate(argv) if arg == '--build-target'],
                                 ['Aglib', 'Essays'])
                self.assertEqual((root / 'repaired-working-archive').read_text(), 'repaired derived archive')
                self.assertEqual((root / 'lake-native-cache.tar').exists(), status == 0)
                self.assertEqual((root / 'outputs').exists(), status == 0)
                if status == 0:
                    self.assertEqual((root / 'outputs').read_text(), 'staged=true\n')
                    with tarfile.open(root / 'lake-native-cache.tar') as archive:
                        self.assertIn('./outputs.jsonl', archive.getnames())
                        self.assertIn('./producer.json', archive.getnames())
                else:
                    self.assertFalse(publish(build='failure'))


if __name__ == '__main__':
    unittest.main()
