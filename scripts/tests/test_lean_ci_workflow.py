"""Exercise native workflow failure gates without running Lean (requires PyYAML)."""
import os
import io
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile
import tomllib
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = yaml.safe_load((ROOT / '.github/workflows/lean-ci.yml').read_text())
JOBS = WORKFLOW['jobs']


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
            success = {'needs.build.result': 'success', 'steps.restore-cache.outcome': 'success',
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

    def test_cache_fallback_reuses_changed_pins_and_existing_key_generations(self):
        restore = next(item for item in JOBS['build']['steps'] if item.get('id') == 'restore')['with']
        values = {'runner.os': 'Linux', 'runner.arch': 'X64', 'github.sha': 'commit',
                  'github.run_id': 'run', 'github.run_attempt': '1',
                  "hashFiles(format('{0}/lean-toolchain', inputs.package-directory))": 'compiler',
                  "hashFiles(format('{0}/lake-manifest.json', inputs.package-directory))": 'pins',
                  "hashFiles(format('{0}/lean-toolchain', inputs.package-directory), "
                  "format('{0}/lake-manifest.json', inputs.package-directory))": 'legacy-pins'}

        def render(text):
            return re.sub(r'\$\{\{\s*(.*?)\s*\}\}',
                          lambda match: values[match[1]], text)

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
            ['bash', '-e', '-o', 'pipefail', '-c', 'lake() { printf "%s\\n" "$*"; }\n' + build['run']],
            env={**os.environ, 'BUILD_TARGETS': 'R5Lab Essays', 'CHECK_TARGETS': 'Checks',
                 'RUNNER_TEMP': '/fixture'}, capture_output=True, text=True)
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

    def run_restore(self, *, offline=False):
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
                               'FIXTURE': str(self.root), 'OFFLINE': str(int(offline))},
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
                    env={**os.environ, 'BUILD_TARGETS': 'Aglib Quillen'},
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
                           'LAKE_CACHE_DIR': directory + '/cache', 'CLONE_STATUS': '0',
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

    def test_build_artifact_contains_only_mathematical_outputs(self):
        upload = next(item for item in JOBS['build']['steps']
                      if item.get('uses', '').startswith('actions/upload-artifact@'))
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


if __name__ == '__main__':
    unittest.main()
