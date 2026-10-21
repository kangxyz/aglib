"""Actual hosted Adapter.plan recovery ordering without Lean or network."""
import json
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch

from lean_ci.configured import create_application
from lean_ci.project import dependencies
from tests.project.test_configuration import Fixture


class PlanningSourceRecoveryTests(Fixture):
    def setUp(self):
        super().setUp()
        self.external = tempfile.TemporaryDirectory(prefix='lean-ci-planning-git-')
        self.addCleanup(self.external.cleanup)
        self.upstream = Path(self.external.name)
        self.a = self.repository('a', {'lakefile.toml': 'name="Aglib"\n[[lean_lib]]\nname="Aglib"\n',
                                       'Aglib/Provider.lean': 'import Mathlib.X\n'})
        self.b = self.repository('b', {'lakefile.toml': 'name="mathlib"\n[[lean_lib]]\nname="Mathlib"\n',
                                       'Mathlib/X.lean': 'import Init\ndef x := 1\n'})
        self.a_pin = self.pin('Aglib', self.a)
        self.old_b = self.pin('mathlib', self.b)
        (self.b / 'Mathlib/X.lean').write_text('import Init\ndef x := 2\n')
        self.external_commit(self.b)
        self.new_b = self.pin('mathlib', self.b)
        self.write('examples/downstream/lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('examples/downstream/lakefile.toml', 'name="client"\n[[lean_lib]]\nname="Consumer"\n')
        with (self.root / '.github/lean-ci.toml').open('a') as stream:
            stream.write('[[clients]]\nid="downstream"\npath="examples/downstream"\n[clients.roles]\nproduction=["Consumer"]\n')
        self.write('Tiny/Base.lean', 'import Aglib.Provider\ndef base := 1\n')
        self.write('Tiny/Unrelated.lean', 'import Init\ndef unrelated := 0\n')
        self.write('examples/downstream/Consumer.lean', 'import Mathlib.X\ndef direct := 0\n')
        self.write('examples/downstream/Consumer/Indirect.lean', 'import Tiny.Consumer\ndef indirect := 0\n')
        self.write('.gitignore', '.lake/\n')
        self.configure(self.old_b)
        self.base = self.commit()
        self.configure(self.new_b)
        self.head = self.commit()

    def external_git(self, directory, *arguments):
        return subprocess.check_output(['git', *arguments], cwd=directory, stderr=subprocess.DEVNULL).decode().strip()

    def external_commit(self, directory):
        self.external_git(directory, 'add', '.')
        self.external_git(directory, '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                          '-c', 'commit.gpgsign=false', 'commit', '-qm', 'fixture')

    def repository(self, name, files):
        directory = self.upstream / name
        directory.mkdir()
        self.external_git(directory, 'init', '-q')
        for path, source in files.items():
            target = directory / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(source)
        self.external_commit(directory)
        return directory

    def pin(self, name, directory):
        revision = self.external_git(directory, 'rev-parse', 'HEAD')
        return {'name': name, 'type': 'git', 'url': str(directory),
                'rev': revision, 'inputRev': revision, 'inherited': False, 'subDir': None}

    def configure(self, mathlib):
        self.write('lakefile.toml', 'name="Tiny"\n[[lean_lib]]\nname="Tiny"\n[[lean_lib]]\nname="TinyTest"\n'
                   + ''.join(f'[[require]]\nname="{p["name"]}"\ngit="{p["url"]}"\nrev="{p["rev"]}"\n'
                             for p in (self.a_pin, mathlib)))
        self.write('lake-manifest.json', json.dumps({'name': 'Tiny', 'packages': [self.a_pin, mathlib]}))

    def test_cold_hosted_plan_resolves_once_then_pure_revalidation_is_narrow(self):
        self.assertFalse((self.root / '.lake').exists())
        application = create_application(self.root)
        original = dependencies.resolve_planning_sources
        before = {path.relative_to(self.root).as_posix(): path.read_bytes()
                  for path in self.root.rglob('*') if path.is_file() and '.git' not in path.parts}
        commands, run = [], subprocess.run
        def source_only(command, **kwargs):
            commands.append(command)
            self.assertEqual(Path(command[0]).name, 'git', 'planning launched a compiler/build')
            return run(command, **kwargs)
        def acquire(root, config, base):
            return original(root, config, base, allow_local=True)
        with patch('lean_ci.transport.history.select_baseline', return_value={'kind': 'verified', 'base': self.base}), \
                patch.object(dependencies, 'resolve_planning_sources', side_effect=acquire) as resolver, \
                patch.object(subprocess, 'run', side_effect=source_only):
            payload = application.adapter.plan(self.root, 'fixture/project', 'main', self.head)
            application.adapter.validate_plan(self.root, dict(payload, head=self.head))
        self.assertEqual(resolver.call_count, 1)
        scope = payload['scope']
        self.assertIn('Tiny.Base', scope['modules'])
        self.assertIn('TinyTest.Positive', scope['tests'])
        self.assertIn('downstream:Consumer', scope['clients']['downstream'])
        self.assertIn('downstream:Consumer.Indirect', scope['clients']['downstream'])
        self.assertNotIn('Tiny.Unrelated', scope['modules'])
        self.assertFalse(scope['initial'])
        self.assertEqual(self.git('rev-parse', 'HEAD'), self.head)
        self.assertEqual(self.git('status', '--porcelain'), '')
        self.assertTrue(commands)
        self.assertEqual(before, {path: (self.root / path).read_bytes() for path in before})
        self.assertFalse((self.root / '.lake/build').exists())

    def test_source_acquisition_failure_propagates_and_is_not_initialization(self):
        application = create_application(self.root)
        with patch('lean_ci.transport.history.select_baseline', return_value={'kind': 'verified', 'base': self.base}), \
                patch.object(dependencies, 'resolve_planning_sources', side_effect=ValueError('source unavailable')) as resolver:
            with self.assertRaisesRegex(ValueError, 'source unavailable'):
                application.adapter.plan(self.root, 'fixture/project', 'main', self.head)
        resolver.assert_called_once()

    def test_ordinary_doc_plan_never_acquires_dependency_sources(self):
        base = self.head
        self.write('README.md', 'Documentation only.\n')
        head = self.commit()
        application = create_application(self.root)
        with patch('lean_ci.transport.history.select_baseline', return_value={'kind': 'verified', 'base': base}), \
                patch.object(dependencies, 'resolve_planning_sources') as resolver:
            payload = application.adapter.plan(self.root, 'fixture/project', 'main', head)
        resolver.assert_not_called()
        self.assertEqual(payload['scope']['modules'], [])
