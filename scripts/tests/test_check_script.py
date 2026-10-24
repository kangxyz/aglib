"""The retained shell entry forwards to the package without another executor."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'check.sh'


class CheckScriptTests(unittest.TestCase):
    def test_native_command_list_contains_the_existing_ci_checks(self):
        result = subprocess.run(['bash', str(SCRIPT), '--list'], text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        commands = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertIn(['lake', '--rehash', 'build', 'Aglib'], commands)
        self.assertIn(['lake', 'test'], commands)
        self.assertIn(['lake', '--no-build', 'lint', 'Aglib', '--', '--trace'], commands)
        self.assertEqual(commands[-1], ['lake', 'env', '<pinned-axiom-audit>', '--root', 'Aglib'])
        self.assertEqual(len([c for c in commands if 'build' in c]), 2)

    def test_shell_forwards_arguments_and_exit_status_without_changing_environment(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); scripts = root / 'scripts'; scripts.mkdir()
            entry = scripts / 'check.sh'; entry.write_bytes(SCRIPT.read_bytes())
            binary = root / 'bin'; binary.mkdir()
            python = binary / 'python3'
            python.write_text('#!/bin/sh\nprintf "%s\\n" "$*" "$PYTHONPATH" > "$TRACE"\nexit 19\n')
            python.chmod(0o755)
            result = subprocess.run(['bash', str(entry), '--base', 'accepted', '--source-only'],
                env={**os.environ, 'PATH': str(binary) + ':' + os.environ['PATH'],
                     'PYTHONPATH': '/unchanged/remote/profile', 'TRACE': str(root / 'trace')})
            self.assertEqual(result.returncode, 19)
            log = (root / 'trace').read_text()
            self.assertIn('scripts/lean_tools/__main__.py check --root', log)
            self.assertIn('--base accepted --source-only', log)
            self.assertTrue(log.rstrip().endswith('/unchanged/remote/profile'))


if __name__ == '__main__':
    unittest.main()
