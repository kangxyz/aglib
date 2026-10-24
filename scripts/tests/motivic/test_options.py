# Authors: kangxyz
"""Policy and dispatcher coverage independent of Lean and Git."""
from contextlib import redirect_stderr, redirect_stdout
import io
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

from lean_ci import source
from lean_ci import motivic
from lean_ci.motivic import sources


class PolicyTests(unittest.TestCase):
    def test_shared_header_grammar_is_the_only_lexical_implementation(self):
        self.assertIs(sources.lean_imports, source.lean_imports)
        self.assertIs(sources.is_import_surface, source.is_import_surface)
        self.assertEqual(sources.lean_imports('module\npublic import Motivic.Core\n'
                                            'def text := "import Motivic.Noise"\n'),
                         ['Motivic.Core'])

    def test_resource_overrides_preserve_motivic_precedence_and_parent_profile(self):
        with patch.dict(os.environ, {'MOTIVIC_BUILD_THREADS': '3', 'AGLIB_BUILD_THREADS': '8',
                                   'R5_LEAN_REMOTE_PROFILE': 'inherited'}, clear=True):
            environment = motivic.runtime_environment()
        self.assertEqual(environment['AGLIB_BUILD_THREADS'], '3')
        self.assertEqual(environment['R5_LEAN_REMOTE_PROFILE'], 'inherited')
        config = motivic.resource_config()
        self.assertEqual(config.value(environment, 'build_thread'), '3')
        self.assertIn('R5_LEAN_REMOTE_PROFILE', config.names('profile'))
        self.assertIn('AGLIB_LEAN_MEMORY_MB', config.names('memory'))
        self.assertIn('AGLIB_RSS_LIMIT_MB', config.names('rss'))

    def test_dispatcher_is_lazy_and_forwards_root_and_arguments(self):
        with patch('lean_ci.motivic.repository.main', return_value=9) as main:
            self.assertEqual(motivic.main(['repository', '--root', '/fixture']), 9)
        main.assert_called_once_with(['--root', '/fixture'])
        with redirect_stderr(io.StringIO()):
            self.assertEqual(motivic.main(['unknown']), 2)

    def test_package_options_name_only_source_policy_dependencies(self):
        from lean_ci.local import SourceCheck
        root = Path('/fixture')
        result = motivic.options(root)
        self.assertEqual(result['production'], ('Motivic',))
        self.assertEqual(result['check_targets'], ())
        check, = result['source_checks']
        self.assertIsInstance(check, SourceCheck)
        self.assertEqual(check.command, (sys.executable, str(Path(__file__).resolve().parents[2] / 'lean_ci/__main__.py'), 'motivic',
                                        'repository', '--root', '/fixture'))
        self.assertEqual({Path(path).name for path in check.inputs},
                         {'__init__.py', 'repository.py', 'imports.py', 'sources.py', 'source.py', 'cli.py', '__main__.py'})
        self.assertTrue(all(Path(path).is_file() for path in check.inputs))


if __name__ == '__main__':
    unittest.main()
