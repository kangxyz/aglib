#!/usr/bin/env python3
"""Real, local two-module Lean CI/cache integration; run under a native lease.

All fixture sources, caches and evidence live beneath --state. This is an
explicit-full local fixture, never a verified GitHub baseline enrollment.
"""
import argparse
from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys

from lean_ci.engine import Application, implementation_identity
from lean_ci.resources import ResourceConfig
from lean_ci.runtime import NativeRuntime, command_matches
from lean_ci.state import check_binding, file_hash, read_json, write_json


MODULES = ['Quartz.Upstream', 'Quartz']
SOURCE_POLICY = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'Check.lean']
UPSTREAM = 'module\nnamespace Quartz\npublic def upstream : Nat := {value}\nend Quartz\n'
ROOT_SOURCE = ('module\npublic import Quartz.Upstream\nnamespace Quartz\n'
               'public theorem nonnegative : 0 ≤ upstream := Nat.zero_le upstream\nend Quartz\n')
CHECK_SOURCE = 'import Quartz\nexample : 0 ≤ Quartz.upstream := Quartz.nonnegative\n'
PACKAGE = ('name = "quartzFixture"\nversion = "0.1.0"\ndefaultTargets = ["Quartz"]\n'
           'moreLeanArgs = ["-DwarningAsError=true"]\nenableArtifactCache = true\n'
           'restoreAllArtifacts = true\n\n[[lean_lib]]\nname = "Quartz"\n')


def require(condition, message):
    if not condition:
        raise ValueError(message)


@contextmanager
def native_lease(path):
    """A busy shared lease fails immediately; it never queues native work."""
    if path is None:
        yield
        return
    require(path.is_absolute(), '--lease must be an absolute path')
    with path.open('a+') as stream:
        fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        try:
            yield
        finally:
            fcntl.flock(stream.fileno(), fcntl.LOCK_UN)


def git(root, *arguments):
    environment = dict(os.environ, GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                       GIT_AUTHOR_NAME='Lean CI fixture', GIT_COMMITTER_NAME='Lean CI fixture',
                       GIT_AUTHOR_EMAIL='fixture@example.invalid', GIT_COMMITTER_EMAIL='fixture@example.invalid',
                       GIT_AUTHOR_DATE='2000-01-01T00:00:00+0000', GIT_COMMITTER_DATE='2000-01-01T00:00:00+0000')
    return subprocess.check_output(['git', *arguments], cwd=root, env=environment, text=True).strip()


def commit(root, message):
    git(root, 'add', '--', '.')
    git(root, '-c', 'commit.gpgSign=false', 'commit', '--no-verify', '-qm', message)
    return git(root, 'rev-parse', 'HEAD')


def create_fixture(root, toolchain):
    root.mkdir()
    (root / 'Quartz').mkdir()
    (root / '.lake/packages').mkdir(parents=True)
    files = {'.gitignore': '.lake/\n', 'lean-toolchain': toolchain + '\n',
             'lakefile.toml': PACKAGE, 'Quartz/Upstream.lean': UPSTREAM.format(value=7),
             'Quartz.lean': ROOT_SOURCE, 'Check.lean': CHECK_SOURCE,
             'lake-manifest.json': json.dumps({'version': '1.2.0', 'packagesDir': '.lake/packages',
                                               'packages': [], 'name': 'quartzFixture', 'lakeDir': '.lake',
                                               'fixedToolchain': False}, indent=2) + '\n'}
    for name, content in files.items():
        (root / name).write_text(content)
    git(root, '-c', 'init.defaultBranch=main', 'init', '-q')
    return commit(root, 'two-module local fixture, upstream seven')


def change_upstream(root):
    before = file_hash(root / 'Quartz.lean')
    (root / 'Quartz/Upstream.lean').write_text(UPSTREAM.format(value=9))
    require(git(root, 'diff', '--name-only') == 'Quartz/Upstream.lean', 'Unexpected changed fixture inputs')
    head = commit(root, 'upstream nine, root theorem source unchanged')
    require(file_hash(root / 'Quartz.lean') == before, 'Root source changed during upstream-only scenario')
    return head


class FixtureAdapter:
    """Explicit full scope; graph freshness remains entirely Lake's decision."""
    def __init__(self, allow_build, late_failure=False):
        self.policy = {'coverage': 'explicit-full-local-fixture', 'allow_build': bool(allow_build),
                       'late_failure': bool(late_failure), 'modules': MODULES,
                       'verified_github_baseline': False}

    def plan(self, root, repository, default_branch, head, requested_base=None, api=None):
        return {'baseline': {'kind': 'explicit-full-local-fixture', 'source_head': head},
                'fixture_policy': self.policy, 'scope': {'native': True}}

    def required_phases(self, root, payload):
        return ['source', 'native']

    def validate_plan(self, root, plan):
        require(plan.get('fixture_policy') == self.policy, 'Fixture policy changed after planning')
        require(plan.get('scope') == {'native': True}, 'Fixture omitted its mandatory native scope')
        require(plan['baseline'] == {'kind': 'explicit-full-local-fixture', 'source_head': plan['head']},
                'Fixture baseline misrepresented its current local source')
        require(json.loads((root / 'lake-manifest.json').read_text())['packages'] == [],
                'Fixture must have no external dependencies')
        require((root / 'lakefile.toml').read_text() == PACKAGE, 'Fixture package policy differs')

    def tasks(self, root, plan, phase, directory):
        def task(name, command, kind='process', **extra):
            return {'id': name, 'kind': kind, 'command': list(map(str, command)), 'cwd': str(root), **extra}
        if phase == 'source':
            return [task('source-diff', ['git', 'diff', '--check'])]
        require(phase == 'native', 'Unknown fixture phase')
        graph = ['lake', '--rehash', '--no-cache']
        if not self.policy['allow_build']:
            graph += ['--no-build']
        result = [task('shared-root-build', graph + ['build', 'Quartz'], kind='graph-build',
                       modules=MODULES, capped=True),
                  task('reflection-environment', ['lake', '--no-cache', 'env', 'printenv', 'LEAN_PATH'],
                       kind='environment', environment_output=str(directory / 'search-path.txt')),
                  task('proof', ['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', 'Check.lean'],
                       kind='check', check_kind='fixture-proof', modules=['Quartz'], capped=True),
                  task('root-graph', ['lake', '--rehash', '--no-cache', '--no-build', 'build', 'Quartz',
                                      '-o', directory / 'native-outputs.jsonl'], capped=True,
                       mapping=str(directory / 'native-outputs.jsonl'), identity_modules=MODULES)]
        if self.policy['late_failure']:
            result.append(task('expected-late-failure', [sys.executable, '-c', 'import sys; sys.exit(1)']))
        return result

    def binding(self, root, task, toolchain, reflection=None, observations=None):
        value = check_binding(root, task['check_kind'], task['modules'], task['command'], SOURCE_POLICY,
                              raw_paths=['Quartz.lean', 'Quartz/Upstream.lean'],
                              toolchain=toolchain, hash_file=observations.hash_file)
        value['fixture_harness'] = observations.hash_file(Path(__file__).absolute())
        value['reflective_imports'] = reflection.closure(['Quartz']) if reflection else None
        return value

    def summary(self, root, plan, records):
        return {'coverage': 'explicit-full-local-fixture', 'verified_github_baseline': False,
                'target_compilation_allowed': self.policy['allow_build']}


class Harness:
    def __init__(self, state, toolchain, resource_config, lease):
        self.state, self.toolchain, self.resource_config = state, toolchain, resource_config
        self.progress = state / 'check-progress'
        self.check_receipts = {}
        self.report = {'schema': 1, 'status': 'running', 'toolchain': toolchain,
                       'implementation': implementation_identity(), 'harness_sha256': file_hash(__file__),
                       'lease': str(lease) if lease else None, 'source_heads': {}, 'attempts': {},
                       'transfers': [], 'limitations': [
                           'Same installed compiler in every scenario; no arbitrary cross-version import claim.',
                           'Explicit-full local fixture, not a verified GitHub baseline.',
                           'Partial native artifacts and proof progress do not establish CI completion.',
                           'No dependencies, services, repository remotes or remote cache metadata are requested.',
                           '--no-cache alone is not a universal no-network guarantee.']}
        self.save()

    def save(self):
        write_json(self.state / 'report.json', self.report)

    def runtime(self, root, cache):
        environment = dict(os.environ, ELAN_TOOLCHAIN=self.toolchain, LAKE_CACHE_DIR=str(cache),
                           LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='true', LAKE_RESTORE_ARTIFACTS='true')
        return NativeRuntime(root, resource_config=self.resource_config, environment=environment)

    def task_evidence(self, application, plan, phase, record):
        directory = Path(record['directory'])
        evidence = []
        specifications = application.adapter.tasks(application.root, plan, phase, directory)
        completed = {item['id']: item for item in record['tasks']}
        for index, task in enumerate(specifications):
            receipt_path = directory / f'task-{index:04d}' / 'resource.json'
            item = completed.get(task['id'])
            result = item['result'] if item else None
            entry = {'id': task['id'], 'kind': task['kind'], 'command': task['command'],
                     'receipt_path': str(receipt_path) if receipt_path.is_file() else None,
                     'recorded_completed': item is not None}
            if result and task['kind'] == 'check':
                key, mode = result['success']['key'], result['mode']
                if mode == 'performed':
                    require(receipt_path.is_file(), 'Performed proof lacks its actual resource receipt')
                    self.check_receipts[key] = str(receipt_path)
                entry.update(mode=mode, key=key, original_receipt_path=self.check_receipts.get(key),
                             progress_record=str(self.progress / (key + '.json')))
            if receipt_path.is_file():
                receipt = read_json(receipt_path)
                entry.update(exit_code=receipt.get('exit_code'), guard_failure=receipt.get('guard_failure'),
                             owned_group_gone=receipt.get('owned_group_gone'))
            if result and task.get('mapping'):
                entry.update(mapping=task['mapping'], mapping_sha256=result['mapping_sha256'])
            evidence.append(entry)
        return evidence

    def attempt(self, name, root, cache, *, allow_build, late_failure=False, expected_failure=None):
        state = self.state / 'attempts' / name
        adapter = FixtureAdapter(allow_build, late_failure)
        application = Application(root, adapter, self.runtime(root, cache))
        head = git(root, 'rev-parse', 'HEAD')
        plan = application.plan('local/quartzFixture', 'main', head, state)
        report = {'head': head, 'root': str(root), 'cache': str(cache), 'plan_id': plan['id'],
                  'state': str(state), 'target_compilation_allowed': allow_build}
        self.report['attempts'][name] = report
        self.save()
        source = application.run_phase(state, 'source')
        report['source_tasks'] = self.task_evidence(application, plan, 'source', source)
        self.save()
        try:
            native = application.run_phase(state, 'native', progress=self.progress)
        except ValueError as error:
            require(expected_failure is not None, 'Unexpected native failure: ' + str(error))
            native = read_json(state / 'native.json')
            report['native_error'] = str(error)
        else:
            require(expected_failure is None, 'Expected native failure incorrectly completed')
        report['native_status'] = native['status']
        report['native_tasks'] = self.task_evidence(application, plan, 'native', native)
        self.save()
        if expected_failure:
            failure_id, exit_code = expected_failure
            tasks = adapter.tasks(root, plan, 'native', Path(native['directory']))
            index = next(index for index, task in enumerate(tasks) if task['id'] == failure_id)
            require(native['status'] != 'completed' and len(native['tasks']) == index,
                    'Failure did not occur at the expected actual task')
            failed = read_json(Path(native['directory']) / f'task-{index:04d}' / 'resource.json')
            require(failed.get('state') == 'completed' and failed.get('exit_code') == exit_code
                    and failed.get('guard_failure', 'missing') is None
                    and failed.get('owned_group_gone') is True
                    and failed.get('cwd') == str(root)
                    and command_matches(tasks[index]['command'], failed.get('command', [])),
                    'Expected failure lacks its actual closed-group native receipt')
            try:
                application.finalize(state, state / 'accepted-outputs.jsonl')
            except ValueError as error:
                require('Missing/incomplete/wrong-plan required CI phase' in str(error),
                        'Finalizer failed for a different reason: ' + str(error))
                report['finalize_error'] = str(error)
            else:
                raise ValueError('Incomplete native phase incorrectly finalized')
            require(not (state / 'complete.json').exists() and not (state / 'accepted-outputs.jsonl').exists(),
                    'Incomplete native phase published completion or accepted mappings')
            application.validate_plan(plan)
            report['expected_failure_exit_code'] = exit_code
            report['completion_rejected'] = True
        else:
            summary = application.finalize(state, state / 'accepted-outputs.jsonl')
            require(summary['status'] == 'complete', 'Actual finalizer did not complete')
            report.update(completion=str(state / 'complete.json'),
                          accepted_mappings=str(state / 'accepted-outputs.jsonl'),
                          performed_checks=summary['performed_checks'], reused_checks=summary['reused_checks'])
        self.save()
        return application, plan, native, report

    def transfer(self, name, root, cache, command):
        directory = self.state / 'transfers' / name
        task = {'id': name, 'kind': 'process', 'command': list(map(str, command)),
                'cwd': str(root), 'capped': True}
        result = self.runtime(root, cache).run(task, directory)
        self.report['transfers'].append({'id': name, 'command': task['command'],
                                         'receipt_path': str(directory / 'resource.json'),
                                         'exit_code': result['receipt']['exit_code']})
        self.save()

    def proof(self, report):
        return next(task for task in report['native_tasks'] if task['id'] == 'proof')

    def mapping(self, report):
        return Path(next(task['mapping'] for task in report['native_tasks'] if task['id'] == 'root-graph'))

    def run(self):
        producer, consumer = self.state / 'producer', self.state / 'consumer'
        cache_a, cache_b = self.state / 'cache-a', self.state / 'cache-b'
        cache_a.mkdir(); cache_b.mkdir()
        self.report['source_heads']['producer7'] = create_fixture(producer, self.toolchain)
        producer_root_hash = file_hash(producer / 'Quartz.lean')
        self.save()
        _, _, _, a = self.attempt('producer7-partial', producer, cache_a, allow_build=True,
                                   late_failure=True, expected_failure=('expected-late-failure', 1))
        proof7 = self.proof(a)
        require(proof7['mode'] == 'performed', 'First actual proof check was not performed')
        require(Path(proof7['progress_record']).is_file(), 'Partial proof success was not retained')
        compiler7 = read_json(proof7['progress_record'])['binding']['execution']['toolchain']
        self.report['compiler_content'] = {name: value for name, value in compiler7.items()
                                           if isinstance(value, str)}
        mapping7 = self.mapping(a)
        require(mapping7.is_file(), 'Partial phase lost its successful native mappings')
        stage7 = self.state / 'stage7'
        self.transfer('stage7', producer, cache_a, ['lake', '--no-cache', 'cache', 'stage', mapping7, stage7])
        require(file_hash(stage7 / 'outputs.jsonl') == file_hash(mapping7), 'Stage7 mapping identity differs')

        require(not any(cache_b.iterdir()), 'Consumer cache was not initially empty')
        self.report['source_heads']['consumer7'] = create_fixture(consumer, self.toolchain)
        consumer_root_hash = file_hash(consumer / 'Quartz.lean')
        initial_tree = git(producer, 'rev-parse', 'HEAD^{tree}')
        require(git(consumer, 'rev-parse', 'HEAD^{tree}') == initial_tree,
                'Producer and fresh consumer do not have identical committed source trees')
        self.report['initial_fixture_tree'] = initial_tree
        self.transfer('unstage7', consumer, cache_b, ['lake', '--no-cache', 'cache', 'unstage', stage7])
        _, _, _, b = self.attempt('consumer7-restored', consumer, cache_b, allow_build=False)
        proof_b = self.proof(b)
        require(proof_b['mode'] == 'reused' and proof_b['key'] == proof7['key'],
                'Matching restored native inputs did not reuse the actual partial proof success')
        self.report['matching_cache_restored_without_target_compilation'] = True
        self.save()

        self.report['source_heads']['consumer9'] = change_upstream(consumer)
        progress_before = sorted(path.name for path in self.progress.glob('*.json'))
        _, _, _, c = self.attempt('consumer9-old-cache-only', consumer, cache_b, allow_build=False,
                                   expected_failure=('shared-root-build', 3))
        require(sorted(path.name for path in self.progress.glob('*.json')) == progress_before,
                'An incompatible cache-only failure recorded a new proof success')
        c['old_proof_not_consumed'] = not any(task['recorded_completed'] and task['id'] == 'proof'
                                            for task in c['native_tasks'])
        require(c['old_proof_not_consumed'], 'Old-only cache reached a proof reuse decision')
        self.save()

        self.report['source_heads']['producer9'] = change_upstream(producer)
        _, _, _, d_producer = self.attempt('producer9-current', producer, cache_a, allow_build=True)
        proof9 = self.proof(d_producer)
        require(proof9['mode'] == 'performed' and proof9['key'] != proof7['key'],
                'Changed upstream incorrectly reused the old proof binding')
        require(read_json(proof9['progress_record'])['binding']['execution']['toolchain'] == compiler7,
                'Compiler/runtime identity changed; this fixture requires one fixed installed compiler')
        current_tree = git(producer, 'rev-parse', 'HEAD^{tree}')
        require(git(consumer, 'rev-parse', 'HEAD^{tree}') == current_tree,
                'Current producer and consumer committed source trees differ')
        self.report['current_fixture_tree'] = current_tree
        mapping9, stage9 = self.mapping(d_producer), self.state / 'stage9'
        self.transfer('stage9', producer, cache_a, ['lake', '--no-cache', 'cache', 'stage', mapping9, stage9])
        require(file_hash(stage9 / 'outputs.jsonl') == file_hash(mapping9), 'Stage9 mapping identity differs')
        self.transfer('unstage9', consumer, cache_b, ['lake', '--no-cache', 'cache', 'unstage', stage9])
        application, plan, native, d_consumer = self.attempt('consumer9-current-cache', consumer, cache_b,
                                                            allow_build=False)
        current_proof = self.proof(d_consumer)
        require(current_proof['key'] != proof7['key'], 'Current-input validation reused the old proof key')
        if current_proof['mode'] == 'performed':
            state = Path(d_consumer['state'])
            rerun = application.run_phase(state, 'native', progress=self.progress)
            evidence = self.task_evidence(application, plan, 'native', rerun)
            retry_proof = next(task for task in evidence if task['id'] == 'proof')
            require(retry_proof['mode'] == 'reused' and retry_proof['key'] == current_proof['key'],
                    'Compatible current proof success did not reuse on retry')
            summary = application.finalize(state, state / 'accepted-outputs.jsonl')
            d_consumer['followup_reuse'] = {'native_tasks': evidence,
                                           'reused_checks': summary['reused_checks']}
        require(file_hash(producer / 'Quartz.lean') == producer_root_hash
                and file_hash(consumer / 'Quartz.lean') == consumer_root_hash,
                'Root theorem source changed during upstream artifact propagation')
        self.report.update(status='passed', upstream_artifact_propagation=True,
                           root_theorem_source_unchanged=True, old_proof_key=proof7['key'],
                           current_proof_key=current_proof['key'])
        self.save()
        return self.report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--state', type=Path, required=True, help='fresh absolute scratch directory')
    parser.add_argument('--lease', type=Path, help='optional absolute shared native lease; fail immediately if busy')
    parser.add_argument('--toolchain', help='otherwise read lean-toolchain from the invoking working directory')
    parser.add_argument('--resource-prefix', default='LEAN_CI')
    parser.add_argument('--profile-key', action='append', default=[])
    args = parser.parse_args(argv)
    harness = None
    try:
        require(args.state.is_absolute(), '--state must be an absolute path')
        require(not args.state.exists(), '--state must be fresh and must not already exist')
        toolchain = args.toolchain if args.toolchain is not None else (Path.cwd() / 'lean-toolchain').read_text().strip()
        require(bool(toolchain) and '\n' not in toolchain and '\r' not in toolchain, 'Expected one exact toolchain pin')
        config = ResourceConfig(prefix=args.resource_prefix, profile_keys=tuple(args.profile_key))
        with native_lease(args.lease):
            state = args.state.resolve()
            state.mkdir(parents=True, exist_ok=False)
            harness = Harness(state, toolchain, config, args.lease)
            report = harness.run()
        print(json.dumps({'status': report['status'], 'report': str(state / 'report.json')}, sort_keys=True))
        return 0
    except BlockingIOError as error:
        print('Native lease is busy; no native work was queued: ' + str(error), file=sys.stderr)
        return 75
    except (OSError, ValueError, KeyError, TypeError, StopIteration, subprocess.SubprocessError) as error:
        if harness is not None:
            harness.report.update(status='failed', error=str(error))
            harness.save()
        print('Native integration failed closed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
