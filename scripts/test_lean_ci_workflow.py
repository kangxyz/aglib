"""Exercise native workflow failure gates without running Lean (requires PyYAML)."""
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile
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
        for build in ('success', 'failure', 'skipped', 'cancelled'):
            for imports in ('success', 'failure', 'skipped', 'cancelled'):
                with self.subTest(build=build, imports=imports):
                    result = report(('build', 'Report Build result'),
                                    {'RESULT': build, 'IMPORTS': imports})
                    self.assertEqual(result == 0, build == imports == 'success')

    def test_setup_or_build_failure_prevents_downstream_job(self):
        # Setup failure skips Build, whose report then fails; imports failure also
        # fails that report. None may start checks against partial native output.
        for result in ('success', 'failure', 'skipped', 'cancelled'):
            with self.subTest(result=result):
                allowed = condition(JOBS['test_lint']['if'], {'needs.build.result': result})
                self.assertEqual(allowed, result == 'success')

    def test_lint_feedback_survives_test_failure_but_requires_prerequisites(self):
        for name in ('Lint', 'Mathlib text style', 'Audit production axioms'):
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
        success = dict.fromkeys(('COMPILED', 'TEST', 'LINT', 'STYLE', 'AXIOMS'), 'success')
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
                      step('test_lint', 'Mathlib text style')['run'])
        self.assertIn('lake --no-build lint "${roots[@]}" -- --trace',
                      step('test_lint', 'Lint')['run'])
        self.assertEqual(step('test_lint', 'Test')['run'], 'lake test')
        self.assertIn('--root "$root"', step('test_lint', 'Audit production axioms')['run'])


class RootSelectionAndPublication(unittest.TestCase):
    def test_lint_commands_pass_all_roots_as_native_arguments(self):
        for name, expected in (
                ('Lint', ['--no-build', 'lint', 'Aglib', 'Quillen', '--', '--trace']),
                ('Mathlib text style', ['--no-build', 'exe', 'mathlib/lint-style', 'Aglib', 'Quillen'])):
            with self.subTest(step=name):
                result = subprocess.run(
                    ['bash', '-e', '-o', 'pipefail', '-c',
                     'lake() { printf "%s\\n" "$@"; }\n' + step('test_lint', name)['run']],
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
