"""Generic state API checks without repository adapters or native processes."""
from pathlib import Path
import tempfile
import unittest

from lean_ci.state import Progress, TemporalInputs, arguments_match


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


if __name__ == '__main__':
    unittest.main()
