"""Exercise native workflow failure gates without running Lean (requires PyYAML)."""
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile
import tomllib
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[1]
JOBS = yaml.safe_load((ROOT / '.github/workflows/lean-ci.yml').read_text())['jobs']


def step(job, name):
    return next(item for item in JOBS[job]['steps'] if item.get('name') == name)


def condition(expression, values, *, success=True, cancelled=False):
    """Evaluate this workflow's conditions, including implicit success()."""
    text = expression.removeprefix('${{').removesuffix('}}').strip()
    explicit_status = re.search(r'\b(always|cancelled|success|failure)\(', text)
    if not explicit_status and not success:
        return False
    text = re.sub(r'\b(?:needs|steps|github)(?:\.[\w-]+)+',
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

    def test_build_report_requires_real_build_and_generated_entries(self):
        success = dict.fromkeys(('TOOLS', 'IMPORTS', 'STYLE', 'RESULT'), 'success')
        self.assertEqual(report(('build', 'Report Build result'), success), 0)
        for check in success:
            for outcome in ('failure', 'skipped', 'cancelled'):
                with self.subTest(check=check, outcome=outcome):
                    result = report(('build', 'Report Build result'),
                                    {**success, check: outcome})
                    self.assertNotEqual(result, 0)
                    self.assertFalse(publish(build='failure'))

    def test_setup_or_build_failure_prevents_downstream_job(self):
        # Setup failure skips Build, whose report then fails; imports failure also
        # fails that report. None may start checks against partial native output.
        for result in ('success', 'failure', 'skipped', 'cancelled'):
            with self.subTest(result=result):
                allowed = condition(JOBS['test_lint']['if'], {'needs.build.result': result})
                self.assertEqual(allowed, result == 'success')

    def test_lint_feedback_survives_test_failure_but_requires_prerequisites(self):
        for name in ('Lint', 'Audit production axioms'):
            for build, restore, setup, compiled in (
                    ('success', 'success', 'success', 'success'),
                    ('failure', 'success', 'success', 'success'),
                    ('success', 'failure', 'success', 'success'),
                    ('success', 'success', 'failure', 'success'),
                    ('success', 'skipped', 'skipped', 'skipped'),
                    ('success', 'success', 'success', 'failure'),
                    ('success', 'success', 'success', 'skipped'),
                    ('success', 'success', 'success', 'cancelled')):
                with self.subTest(step=name, build=build, restore=restore, setup=setup):
                    values = {'needs.build.result': build,
                              'steps.restore-cache.outcome': restore,
                              'steps.lean-setup.outcome': setup,
                              'steps.compiled.outcome': compiled}
                    allowed = condition(step('test_lint', name)['if'], values, success=False)
                    self.assertEqual(allowed, build == restore == setup == compiled == 'success')
                    self.assertFalse(condition(step('test_lint', name)['if'], values,
                                               success=False, cancelled=True))

    def test_each_check_failure_or_skip_fails_report_and_blocks_publication(self):
        success = dict.fromkeys(('COMPILED', 'TEST', 'LINT', 'AXIOMS'), 'success')
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
            self.assertTrue(condition(step(job, name)['if'], {}, success=False))
            self.assertTrue(condition(step(job, name)['if'], {}, success=False, cancelled=True))

    def test_each_job_restores_native_and_lake_cache_once_together(self):
        for name in ('build', 'test_lint'):
            restores = [item for item in JOBS[name]['steps']
                        if item.get('uses', '').startswith('actions/cache/restore@')]
            self.assertEqual(len(restores), 1, name)
            paths = restores[0]['with']['path'].splitlines()
            self.assertEqual(paths, ['${{ inputs.package-directory }}/.lake',
                                     '${{ runner.temp }}/lake-native-cache'])
        self.assertNotIn('native-key', [item.get('id') for item in JOBS['build']['steps']])

    def test_native_checks_and_full_text_style_are_preserved(self):
        self.assertIn('mathlib/mk_all --lib "$root" --check',
                      step('build', 'Check generated library entries')['run'])
        self.assertIn('lake --no-build exe mathlib/lint-style "${roots[@]}"',
                      step('build', 'Mathlib text style')['run'])
        self.assertIn('lake --no-build lint "${roots[@]}" -- --trace',
                      step('test_lint', 'Lint')['run'])
        self.assertEqual(step('test_lint', 'Test')['run'], 'lake test')
        self.assertIn('--root "$root"', step('test_lint', 'Audit production axioms')['run'])


class PreflightAndLintTimeout(unittest.TestCase):
    def test_preflights_run_once_before_production_and_gate_failures(self):
        names = ['Prepare check tools', 'Check generated library entries', 'Mathlib text style', 'Build']
        steps = [item for item in JOBS['build']['steps'] if item.get('name') in names]
        self.assertEqual([item['name'] for item in steps], names)
        self.assertEqual(set(JOBS), {'build', 'test_lint', 'upload_cache'})
        self.assertEqual(JOBS['upload_cache']['name'], 'Publish cache')
        self.assertEqual(sum(item.get('name') == 'Mathlib text style'
                             for job in JOBS.values() for item in job['steps']), 1)
        self.assertFalse(any(item.get('id') == 'style' for item in JOBS['test_lint']['steps']))
        self.assertEqual(step('build', 'Prepare check tools')['run'],
                         'lake build batteries/runLinter mathlib/lint-style mathlib/mk_all')
        mock = r'''
lake() {
  printf '%s\n' "$*" >> "$TRACE"
  if test "$1" = build && test "$2" = batteries/runLinter; then return "$TOOLS_STATUS"; fi
  if test "$1" = --no-build && test "$3" = mathlib/mk_all; then return "$IMPORTS_STATUS"; fi
  if test "$1" = --no-build && test "$3" = mathlib/lint-style; then return "$STYLE_STATUS"; fi
  return 0
}
'''
        for tools, imports, style, prerequisite in (
                (0, 0, 0, True), (0, 1, 0, True), (0, 0, 1, True),
                (0, 1, 1, True), (1, 0, 0, True), (0, 0, 0, False)):
            with self.subTest(tools=tools, imports=imports, style=style, setup_cache_ok=prerequisite):
                with tempfile.TemporaryDirectory(prefix='lean-ci-preflight-') as directory:
                    trace = Path(directory) / 'trace'
                    trace.touch()
                    values = {f'steps.{name}.outcome': 'skipped'
                              for name in ('tools', 'imports', 'style', 'build')}
                    healthy = prerequisite
                    executed = []
                    for item in steps:
                        allowed = condition(item['if'], values, success=healthy) if 'if' in item else healthy
                        if not allowed:
                            continue
                        result = subprocess.run(
                            ['bash', '-e', '-o', 'pipefail', '-c', mock + item['run']],
                            env={**os.environ, 'BUILD_TARGETS': 'Aglib Quillen',
                                 'RUNNER_TEMP': directory, 'TRACE': str(trace),
                                 'TOOLS_STATUS': str(tools), 'IMPORTS_STATUS': str(imports),
                                 'STYLE_STATUS': str(style)},
                            capture_output=True, text=True, check=False)
                        values[f"steps.{item['id']}.outcome"] = 'success' if result.returncode == 0 else 'failure'
                        if result.returncode and not item.get('continue-on-error', False):
                            healthy = False
                        executed.append(item['name'])
                    expected_build = prerequisite and tools == imports == style == 0
                    self.assertEqual('Build' in executed, expected_build)
                    if prerequisite and tools == 0:
                        self.assertEqual(executed[:3], names[:3])
                        commands = trace.read_text().splitlines()
                        self.assertEqual(commands[1:4], [
                            '--no-build exe mathlib/mk_all --lib Aglib --check',
                            '--no-build exe mathlib/mk_all --lib Quillen --check',
                            '--no-build exe mathlib/lint-style Aglib Quillen'])
                        self.assertEqual(commands[0], step('build', 'Prepare check tools')['run'].removeprefix('lake '))
                        if expected_build:
                            self.assertEqual(commands[4], f'build Aglib Quillen -o {directory}/outputs.jsonl')
                    if not expected_build:
                        self.assertFalse(publish(build='failure'))
                    self.assertTrue(condition(step('build', 'Save compilation independently of Test and lint')['if'],
                                              {}, success=False))

    def test_failed_skipped_or_cancelled_preflight_never_allows_build(self):
        success = dict.fromkeys(('steps.tools.outcome', 'steps.imports.outcome', 'steps.style.outcome'), 'success')
        for key in success:
            for outcome in ('failure', 'skipped', 'cancelled'):
                self.assertFalse(condition(step('build', 'Build')['if'], {**success, key: outcome}))
        self.assertFalse(condition(step('build', 'Build')['if'], success, cancelled=True))

    def test_lint_only_retries_one_timeout_and_preserves_final_status(self):
        lint = step('test_lint', 'Lint')
        self.assertEqual(lint['timeout-minutes'], 25)
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
                             'FIRST': str(first), 'SECOND': str(second)},
                        capture_output=True, text=True, check=False)
                    self.assertEqual(result.returncode, expected, result.stderr)
                    self.assertEqual(trace.read_text().splitlines(), [
                        '--kill-after=30s 10m env LEAN_ABORT_ON_PANIC=1 lake --no-build lint Aglib Quillen -- --trace'
                    ] * attempts)


class RootSelectionAndPublication(unittest.TestCase):
    def test_lint_commands_pass_all_roots_as_native_arguments(self):
        for job, name, expected in (
                ('test_lint', 'Lint', ['--no-build', 'lint', 'Aglib', 'Quillen', '--', '--trace']),
                ('build', 'Mathlib text style', ['--no-build', 'exe', 'mathlib/lint-style', 'Aglib', 'Quillen'])):
            with self.subTest(step=name):
                result = subprocess.run(
                    ['bash', '-e', '-o', 'pipefail', '-c',
                     'lake() { printf "%s\\n" "$@"; }\n'
                     'timeout() { shift; shift; shift; shift; "$@"; }\n' + step(job, name)['run']],
                    env={**os.environ, 'BUILD_TARGETS': 'Aglib Quillen'},
                    capture_output=True, text=True, check=False)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.splitlines(), expected)

    def test_new_release_includes_asset_and_never_becomes_latest(self):
        self.run_publication(exists=False)

    def test_existing_release_appends_asset(self):
        self.run_publication(exists=True)

    def test_release_failures_are_not_masked(self):
        for exists in (False, True):
            with self.subTest(exists=exists):
                self.run_publication(exists=exists, status=1)

    def run_publication(self, *, exists, status=0):
        with tempfile.TemporaryDirectory(prefix='lean-ci-release-') as directory:
            root = Path(directory)
            (root / 'lake-native-cache.tar').write_text('native artifact')
            mock = r'''
gh() {
  printf '%s\n' "$*" >> "$TRACE"
  if test "$2" = view; then return "$VIEW_STATUS"; fi
  test -s "$ASSET" || return 99
  return "$PUBLISH_STATUS"
}
'''
            result = subprocess.run(
                ['bash', '-e', '-o', 'pipefail', '-c',
                 mock + step('upload_cache', 'Publish staged compilation')['run']],
                cwd=root, env={**os.environ, 'TRACE': directory + '/trace',
                               'VIEW_STATUS': '0' if exists else '1',
                               'PUBLISH_STATUS': str(status), 'ASSET': 'native-1-1.tar',
                               'REPOSITORY': 'fixture/aglib', 'REVISION': '0123456'},
                capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, status, result.stderr)
            commands = (root / 'trace').read_text().splitlines()
            self.assertEqual(len(commands), 2)
            self.assertTrue(commands[0].startswith('release view lean-native-0123456 '))
            if exists:
                self.assertEqual(commands[1],
                                 'release upload lean-native-0123456 native-1-1.tar --repo fixture/aglib')
            else:
                self.assertTrue(commands[1].startswith(
                    'release create lean-native-0123456 native-1-1.tar '))
                self.assertIn('--latest=false', commands[1])


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
        for target in ('"${targets[@]}"', 'batteries/runLinter', 'mathlib/lint-style', 'mathlib/mk_all'):
            self.assertIn(target, verify['run'])
        for result in ('success', 'failure', 'skipped', 'cancelled'):
            self.assertEqual(condition(step('test_lint', 'Test')['if'], {
                'needs.build.result': 'success', 'steps.compiled.outcome': result}),
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
                        auditor = root / 'axiom-audit'
                        auditor.write_text('#!/bin/sh\nexit 0\n')
                        auditor.chmod(0o755)
                        with tarfile.open(cache / 'axiom-audit.tar', 'w') as stream:
                            stream.add(auditor, arcname='axiom-audit')
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
    def test_pinned_auditor_reuses_checkout_and_incremental_build_outputs(self):
        prepare = step('build', 'Prepare axiom auditor')
        self.assertFalse(prepare.get('continue-on-error', False))
        self.assertEqual(prepare['working-directory'], '${{ inputs.package-directory }}')
        mock = r"""
git() {
  printf 'git:%s\n' "$*" >> "$TRACE"
  if test "$1" = clone; then mkdir -p "${@: -1}/.git"; return 0; fi
  printf '%s\n' "$TOOL_REVISION"
}
lake() {
  printf 'lake:%s\n' "$*" >> "$TRACE"
  test "$TOOL_BUILD_STATUS" = 0 || return "$TOOL_BUILD_STATUS"
  mkdir -p .lake/build/bin
  printf '#!/bin/sh\nexit 0\n' > .lake/build/bin/axiom-audit
  chmod +x .lake/build/bin/axiom-audit
}
"""
        with tempfile.TemporaryDirectory(prefix='lean-ci-auditor-') as directory:
            root = Path(directory)
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            environment = {**os.environ, 'TRACE': directory + '/trace',
                           'LAKE_CACHE_DIR': directory + '/cache',
                           'TOOL_REVISION': '46024e005996495c65ef609368e11ab39c4222e3',
                           'TOOL_BUILD_STATUS': '0'}
            for _ in range(2):
                result = subprocess.run(['bash', '-e', '-o', 'pipefail', '-c', mock + prepare['run']],
                                        cwd=root, env=environment, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
            trace = (root / 'trace').read_text().splitlines()
            self.assertEqual(sum(line.startswith('git:clone ') for line in trace), 1)
            self.assertEqual(trace.count('lake:build'), 2)
            self.assertEqual((root / 'cache/axiom-audit/lean-toolchain').read_text(),
                             (root / 'lean-toolchain').read_text())
            for settings in ({'TOOL_REVISION': 'wrong-pin'}, {'TOOL_BUILD_STATUS': '1'}):
                with self.subTest(settings=settings):
                    result = subprocess.run(
                        ['bash', '-e', '-o', 'pipefail', '-c', mock + prepare['run']],
                        cwd=root, env={**environment, **settings}, capture_output=True, text=True)
                    self.assertNotEqual(result.returncode, 0)
        audit = step('test_lint', 'Audit production axioms')['run']
        self.assertNotIn('git ', audit)
        self.assertNotIn('lake build', audit)

    def test_tool_is_transferred_with_current_run_outputs(self):
        build_steps = JOBS['build']['steps']
        self.assertLess(build_steps.index(step('build', 'Prepare axiom auditor')),
                        build_steps.index(step('build', 'Build')))
        upload = next(item for item in build_steps
                      if item.get('uses', '').startswith('actions/upload-artifact@'))
        self.assertEqual(upload['with']['path'].splitlines(), [
            '${{ runner.temp }}/lake-native-cache.tar', '${{ runner.temp }}/axiom-audit.tar'])
        self.assertIn('tar -cf "$RUNNER_TEMP/axiom-audit.tar"',
                      step('build', 'Stage completed native outputs')['run'])
        restore = step('test_lint', "Restore this run's native Build outputs")['run']
        self.assertIn('test -x "$RUNNER_TEMP/check-tools/axiom-audit"', restore)

    def test_actual_stage_and_restore_preserve_executable_and_require_tool_archive(self):
        with tempfile.TemporaryDirectory(prefix='lean-ci-tool-transfer-') as directory:
            root = Path(directory)
            build = root / 'build'
            cache = root / 'cache'
            build.mkdir()
            binary = cache / 'axiom-audit/.lake/build/bin/axiom-audit'
            binary.parent.mkdir(parents=True)
            binary.write_text('#!/bin/sh\nprintf "audited:%s\\n" "$*"\n')
            binary.chmod(0o755)
            (build / 'outputs.jsonl').write_text('current native outputs')
            mock = r"""
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
            stage_result = subprocess.run(
                ['bash', '-e', '-o', 'pipefail', '-c', mock + step(
                    'build', 'Stage completed native outputs')['run']],
                env={**os.environ, 'RUNNER_TEMP': str(build), 'LAKE_CACHE_DIR': str(cache),
                     'GITHUB_OUTPUT': str(root / 'stage-output')}, capture_output=True, text=True)
            self.assertEqual(stage_result.returncode, 0, stage_result.stderr)
            self.assertEqual((root / 'stage-output').read_text(), 'staged=true\n')
            for tool_archive in ('valid', 'missing', 'invalid'):
                with self.subTest(tool_archive=tool_archive):
                    test = root / tool_archive
                    download = test / 'download'
                    download.mkdir(parents=True)
                    (download / 'lake-native-cache.tar').write_bytes(
                        (build / 'lake-native-cache.tar').read_bytes())
                    if tool_archive == 'valid':
                        (download / 'axiom-audit.tar').write_bytes((build / 'axiom-audit.tar').read_bytes())
                    elif tool_archive == 'invalid':
                        (download / 'axiom-audit.tar').write_text('broken archive')
                    result = subprocess.run(
                        ['bash', '-e', '-o', 'pipefail', '-c', mock + step(
                            'test_lint', "Restore this run's native Build outputs")['run']],
                        env={**os.environ, 'RUNNER_TEMP': str(test), 'LAKE_CACHE_DIR': str(download)},
                        capture_output=True, text=True)
                    self.assertEqual(result.returncode == 0, tool_archive == 'valid', result.stderr)
                    self.assertFalse((download / 'lake-native-cache.tar').exists())
                    self.assertFalse((download / 'axiom-audit.tar').exists())
                    if tool_archive == 'valid':
                        audit = subprocess.run([str(test / 'check-tools/axiom-audit'), '--root', 'Aglib'],
                                               capture_output=True, text=True)
                        self.assertEqual(audit.returncode, 0, audit.stderr)
                        self.assertEqual(audit.stdout, 'audited:--root Aglib\n')

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
                    self.assertEqual(caller['uses'],
                                     'kangxyz/aglib/.github/workflows/lean-ci.yml@'
                                     '6c8f51ca331261f88b33bb9c22ef7d33adf01da4')

    def test_empty_targets_fail_all_native_entries_before_external_commands(self):
        names = [('build', 'Check generated library entries'), ('build', 'Mathlib text style'),
                 ('build', 'Build'), ('test_lint', 'Verify Build outputs without compilation'),
                 ('test_lint', 'Lint'), ('test_lint', 'Audit production axioms')]
        with tempfile.TemporaryDirectory(prefix='lean-ci-empty-targets-') as directory:
            tool = Path(directory) / 'check-tools/axiom-audit'
            tool.parent.mkdir()
            tool.write_text('#!/bin/sh\nexit 99\n')
            tool.chmod(0o755)
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
            tool = Path(directory) / 'check-tools/axiom-audit'
            tool.parent.mkdir()
            tool.write_text('#!/bin/sh\nexit 0\n')
            tool.chmod(0o755)
            mock = r"""
lake() {
  printf '%s\n' "$*" >> "$TRACE"
  test "${@: -1}" != "$FAIL_ROOT"
}
"""
            for failure in ('none', 'Aglib', 'Quillen'):
                trace = Path(directory) / 'trace'
                trace.write_text('')
                result = subprocess.run(
                    ['bash', '-e', '-o', 'pipefail', '-c', mock + step(
                        'test_lint', 'Audit production axioms')['run']],
                    env={**os.environ, 'RUNNER_TEMP': directory, 'BUILD_TARGETS': 'Aglib Quillen',
                         'TRACE': str(trace), 'FAIL_ROOT': failure}, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0 if failure == 'none' else 1, result.stderr)
                self.assertEqual(trace.read_text().splitlines(), [
                    f'env {tool} --root Aglib', f'env {tool} --root Quillen'])


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


if __name__ == '__main__':
    unittest.main()
