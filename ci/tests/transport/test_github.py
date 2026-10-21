"""A differently named library/configuration, real Git, and a fixed API adapter."""
from dataclasses import replace
import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest

from lean_ci.transport.github import (BaselineError, CoreRecipeVersion, EvidenceProtocol,
    reviewed_recipe, select)


def sha(value):
    return hashlib.sha256(value).hexdigest()


class ForeignProtocolTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='foreign-lean-protocol-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.workflow = (b'name: Cobalt proof CI\non: push\njobs:\n  cobalt:\n'
                         b'    name: Cobalt validation\n    runs-on: ubuntu-latest\n    steps:\n'
                         b'      - name: Check the Cobalt graph\n'
                         b'        run: python3 tools/cobalt_native.py native\n'
                         b'      - name: Seal Cobalt coverage\n'
                         b'        run: python3 tools/cobalt_native.py finalize\n')
        self.recipes = {'tools/cobalt_native.py': b'def native(): return "checked"\n',
                        'tools/cobalt_state.py': b'def state(): return "complete"\n'}
        self.workflow_path = '.github/workflows/verify-native.yaml'
        self.git('init', '-qb', 'trunk')
        self.git('config', 'user.name', 'Fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.write('.gitignore', b'.lake/\n')
        self.write(self.workflow_path, self.workflow)
        for path, data in self.recipes.items():
            self.write(path, data)
        self.anchor = self.commit('reviewed native source')
        self.write('README.md', b'Later committed documentation.\n')
        self.head = self.commit('current source')
        self.protocol = EvidenceProtocol(
            workflow_path=self.workflow_path, job_name='Cobalt validation',
            native_step='Check the Cobalt graph', finalize_step='Seal Cobalt coverage',
            workflows={sha(self.workflow): 'core'},
            core_entrypoint_paths=tuple(self.recipes),
            core_recipes=frozenset({tuple(sha(value) for value in self.recipes.values())}))

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True).strip()

    def write(self, path, value):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(value)

    def commit(self, label):
        self.git('add', '.')
        self.git('commit', '-qm', label)
        return self.git('rev-parse', 'HEAD')

    def api(self, missing_final=False, skipped=False):
        owner = self
        class API:
            calls = []
            def get(self, path, **query):
                return {'full_name': 'cobalt-foundation/library', 'default_branch': 'trunk'}

            def pages(self, path, key, **query):
                self.calls.append((path, key, query))
                if key == 'workflow_runs':
                    if path != '/actions/workflows/verify-native.yaml/runs' or query != {'branch': 'trunk', 'status': 'success'}:
                        raise AssertionError((path, query))
                    for run_id, revision in ((2, owner.head), (1, owner.anchor)):
                        yield {'id': run_id, 'run_attempt': 3, 'head_sha': revision,
                               'event': 'push', 'status': 'completed', 'conclusion': 'success',
                               'head_branch': 'trunk', 'path': owner.workflow_path,
                               'head_repository': {'full_name': 'cobalt-foundation/library'},
                               'html_url': f'https://github.example/cobalt/runs/{run_id}'}
                else:
                    run_id = 2 if '/runs/2/' in path else 1
                    steps = [{'name': owner.protocol.native_step, 'status': 'completed',
                              'conclusion': 'skipped' if skipped and run_id == 2 else 'success'}]
                    if not (missing_final and run_id == 2):
                        steps.append({'name': owner.protocol.finalize_step, 'status': 'completed', 'conclusion': 'success'})
                    yield {'name': owner.protocol.job_name, 'run_id': run_id, 'run_attempt': 3,
                           'status': 'completed', 'conclusion': 'success', 'steps': steps}
        return API()

    def choose(self, api=None, protocol=None):
        return select(self.root, 'cobalt-foundation/library', 'trunk', self.head,
                      api=api or self.api(), protocol=protocol or self.protocol)

    def test_foreign_job_steps_workflow_and_default_branch_are_used(self):
        result = self.choose()
        self.assertEqual(result['base'], self.head)
        self.assertEqual(result['default_branch'], 'trunk')
        self.assertEqual(result['workflow_sha256'], sha(self.workflow))
        self.assertEqual(result['recipe_sha256'], {path: sha(data) for path, data in self.recipes.items()})
        self.assertEqual(result['job_evidence']['endpoint'], '/actions/runs/2/attempts/3/jobs')

    def test_missing_finalizer_or_skipped_native_preserves_the_verified_ancestor(self):
        for api in (self.api(missing_final=True), self.api(skipped=True)):
            self.assertEqual(self.choose(api)['base'], self.anchor)

    def test_unknown_exact_recipe_or_workflow_is_never_promoted(self):
        self.write('tools/cobalt_state.py', b'different unenrolled implementation\n')
        self.head = self.commit('unreviewed recipe')
        self.assertEqual(self.choose()['base'], self.anchor)
        self.write(self.workflow_path, self.workflow + b'# unknown identity\n')
        self.head = self.commit('unreviewed workflow')
        self.assertEqual(self.choose()['base'], self.anchor)

    def test_invalid_protocol_cannot_omit_recipe_or_finalization_requirements(self):
        with self.assertRaises(BaselineError):
            replace(self.protocol, core_entrypoint_paths=(), core_recipes=frozenset())
        with self.assertRaises(BaselineError):
            replace(self.protocol, finalize_step=None)
        with self.assertRaises(BaselineError):
            EvidenceProtocol('verify.yaml', 'job', 'native', None, {sha(self.workflow): 'legacy'})

    def test_optional_legacy_source_allowlist_distinguishes_recipe_only_and_exact_source_trust(self):
        legacy = replace(self.protocol, workflows={sha(self.workflow): 'legacy'},
                         legacy_recipes={path: sha(data) for path, data in self.recipes.items()},
                         core_entrypoint_paths=(), core_recipes=frozenset(), legacy_heads=None)
        self.assertEqual(self.choose(protocol=legacy)['base'], self.head)
        exact = replace(legacy, legacy_heads={self.anchor})
        self.assertEqual(exact.legacy_heads, frozenset({self.anchor}))
        self.assertEqual(self.choose(protocol=exact)['base'], self.anchor)
        with self.assertRaises(BaselineError):
            self.choose(protocol=replace(legacy, legacy_heads=frozenset()))
        with self.assertRaises(BaselineError):
            replace(legacy, legacy_heads={'trunk'})

    def test_current_owner_set_binds_every_new_helper(self):
        self.write('tools/new_helper.py', b'new reviewed helper\n')
        current = self.commit('new owner set')
        paths = (*self.recipes, 'tools/new_helper.py')
        values = (*[sha(value) for value in self.recipes.values()], sha(b'new reviewed helper\n'))
        protocol = replace(self.protocol, core_entrypoint_paths=paths, core_recipes={values})
        self.assertIsNotNone(reviewed_recipe(self.root, current, 'core', protocol))
        self.write('tools/new_helper.py', b'unreviewed helper change\n')
        changed = self.commit('changed helper')
        self.assertIsNone(reviewed_recipe(self.root, changed, 'core', protocol))

    def test_historical_explicit_owner_set_survives_absent_new_helpers(self):
        version = CoreRecipeVersion(tuple(self.recipes), self.protocol.core_recipes, {self.anchor})
        protocol = replace(self.protocol,
            core_entrypoint_paths=(*self.recipes, 'tools/not-yet-existing.py'), core_recipes=frozenset(),
            historical_core_recipes=(version,))
        identity = reviewed_recipe(self.root, self.anchor, 'core', protocol)
        self.assertEqual(identity, {path: sha(value) for path, value in self.recipes.items()})
        self.assertIsNone(reviewed_recipe(self.root, self.head, 'core', protocol))
        self.assertIsNone(reviewed_recipe(self.root, self.anchor, 'core',
                                        replace(protocol, historical_core_recipes=())))

    def test_historical_layout_and_protocol_shape_are_exact(self):
        version = CoreRecipeVersion(('tools/other_layout.py',), {(sha(b'wrong layout'),)}, {self.anchor})
        protocol = replace(self.protocol, core_entrypoint_paths=('tools/new.py',), core_recipes=frozenset(),
                           historical_core_recipes=(version,))
        self.assertIsNone(reviewed_recipe(self.root, self.anchor, 'core', protocol))
        with self.assertRaises(BaselineError):
            CoreRecipeVersion(tuple(self.recipes), {(sha(b'short tuple'),)}, {self.anchor})
        with self.assertRaises(BaselineError):
            CoreRecipeVersion(tuple(self.recipes), self.protocol.core_recipes, {'trunk'})
        for heads in (None, frozenset()):
            with self.assertRaises(BaselineError):
                CoreRecipeVersion(tuple(self.recipes), self.protocol.core_recipes, heads)
        with self.assertRaises(BaselineError):
            replace(self.protocol, historical_core_recipes=({'paths': tuple(self.recipes)},))

    def test_selector_does_not_mutate_project_build_progress_or_source(self):
        cached = self.root / '.lake/build/partial.olean'
        cached.parent.mkdir(parents=True)
        cached.write_bytes(b'partial native build')
        before = (cached.read_bytes(), cached.stat().st_mtime_ns, self.git('rev-parse', 'HEAD'))
        self.choose()
        self.assertEqual((cached.read_bytes(), cached.stat().st_mtime_ns, self.git('rev-parse', 'HEAD')), before)


if __name__ == '__main__':
    unittest.main()
