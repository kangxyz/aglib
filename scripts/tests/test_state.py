"""Generic state API checks without repository adapters or native processes."""
from pathlib import Path
from copy import deepcopy
import tempfile
import unittest
from unittest.mock import patch

from lean_tools.state import Progress, TemporalInputs, arguments_match, digest, read_json, write_json


class GenericStateTests(unittest.TestCase):
    def test_direct_capped_lean_receipt_is_compatible_with_its_logical_command(self):
        expected = ['lean', '--run', 'CobaltCheck.lean']
        actual = ['/owned/capped/bin/lean', '--run', 'CobaltCheck.lean']
        self.assertTrue(arguments_match(expected, actual))
        self.assertFalse(arguments_match(expected, ['/owned/bin/other', *actual[1:]]))
        with tempfile.TemporaryDirectory(prefix='generic-check-progress-') as temporary:
            progress = Progress(Path(temporary))
            binding = {'arguments': expected, 'kind': 'foreign-check'}
            receipt = {'state': 'completed', 'exit_code': 0, 'guard_failure': None,
                       'owned_group_gone': True, 'command': actual}
            first = progress.run(lambda: binding, lambda: (receipt, actual))
            second = progress.run(lambda: binding, lambda: self.fail('compatible success must reuse'))
            self.assertEqual(first['mode'], 'performed')
            self.assertEqual(second['mode'], 'reused')

    def test_observer_hashes_once_without_requiring_any_library_configuration(self):
        with tempfile.TemporaryDirectory(prefix='generic-temporal-input-') as temporary:
            path = Path(temporary) / 'checker-runtime'
            path.write_bytes(b'fixed runtime input')
            observations = TemporalInputs()
            first = observations.hash_file(path)
            self.assertEqual(observations.hash_file(path), first)
            self.assertEqual(observations.hash_count, 1)
            observations.assert_stable()

    def test_old_receipt_survives_producer_repair_but_checker_changes_rerun(self):
        with tempfile.TemporaryDirectory(prefix='check-reuse-') as temporary:
            progress = Progress(Path(temporary))
            old = {'arguments': ['checker', 'Quartz'],
                   'execution': {'implementation': {'execution.py': 'old'}, 'cwd': '.'},
                   'reflective_imports': {'digest': 'unchanged-native-inputs'},
                   'raw_inputs': {'ci/lean_ci/execution.py': 'old', 'check.lean': 'fixed'}}
            receipt = {'state': 'completed', 'exit_code': 0, 'guard_failure': None,
                       'owned_group_gone': True, 'command': old['arguments']}
            record = progress.save(old, receipt, old['arguments'])
            (progress.directory / (record['key'] + '.json')).unlink()
            record['key'] = digest(old)
            path = progress.directory / (record['key'] + '.json')
            write_json(path, record)
            original = path.read_bytes()
            current = deepcopy(old)
            current['execution']['implementation']['execution.py'] = 'repaired'
            current['raw_inputs'].pop('ci/lean_ci/execution.py')
            current['raw_inputs']['scripts/lean_tools/execution.py'] = 'repaired'
            with patch('lean_tools.state.read_json', wraps=read_json) as read:
                self.assertEqual(progress.lookup(current), record)
                self.assertEqual(progress.lookup(current), record)
            self.assertEqual(sum(Path(call.args[0]) == path for call in read.call_args_list), 1)
            self.assertEqual(path.read_bytes(), original)
            for key, changed in [('raw_inputs', {'check.lean': 'changed'}),
                                 ('arguments', ['different-checker', 'Quartz'])]:
                different = deepcopy(current)
                if key == 'raw_inputs':
                    different[key].update(changed)
                else:
                    different[key] = changed
                self.assertIsNone(progress.lookup(different))

            control = deepcopy(old)
            control.pop('reflective_imports')
            progress.save(control, receipt, control['arguments'])
            control['execution']['implementation']['execution.py'] = 'repaired'
            control['raw_inputs']['ci/lean_ci/execution.py'] = 'repaired'
            self.assertIsNone(progress.lookup(control))


if __name__ == '__main__':
    unittest.main()
