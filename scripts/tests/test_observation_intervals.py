"""Synthetic interval and binding guards; no compiler or production cache writes."""
import json
import os
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch

from lean_ci.state import (CheckInputs, InputDrift, Progress, ReflectionGraph, TemporalInputs,
                           check_binding, file_hash, write_json)


class ObservationIntervalTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='observation-interval-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.whole = TemporalInputs()
        self.cache, self.metadata = {}, {}
        self.source = self.root / 'Quartz.lean'
        self.source.write_text('module\n')
        self.artifact = self.root / '.lake/build/lib/lean/Quartz.olean'
        self.artifact.parent.mkdir(parents=True)
        self.artifact.write_bytes(b'native output')
        self.policy = self.root / 'policy.py'
        self.policy.write_text('# admitted policy\n')

    def inputs(self):
        return CheckInputs(self.whole, hash_cache=self.cache, metadata_cache=self.metadata)

    def hardlink_roundtrip(self, path):
        time.sleep(.002)
        link = path.with_name(path.name + '.cache-link')
        os.link(path, link)
        link.unlink()

    def restored_write(self, path):
        content, before = path.read_bytes(), path.stat()
        time.sleep(.002)
        path.write_bytes(b'transient mutation')
        path.write_bytes(content)
        os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))

    def fixture(self):
        library = self.artifact.parent
        for suffix in ('.ilean', '.c'):
            output = (self.root / '.lake/build/ir/Quartz.c' if suffix == '.c'
                      else library / ('Quartz' + suffix))
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(b'fixture output')
        write_json(library / 'Quartz.ilean',
                   {'version': 5, 'module': 'Quartz', 'directImports': []})
        write_json(library / 'Quartz.trace',
                   {'schemaVersion': '2025-09-10', 'depHash': '0' * 16,
                    'outputs': {'m': False, 'o': '0' * 16 + '.olean',
                                'i': '0' * 16 + '.ilean', 'c': '0' * 16 + '.c'}})
        return library

    def binding(self, inputs):
        return check_binding(self.root, 'fixture', ['Quartz'], ['lean', 'Quartz.lean'],
                             ['policy.py'], raw_paths=['Quartz.lean'],
                             runtime_modules=['Quartz'], hash_file=inputs.hash_file)

    def test_native_hardlink_between_intervals_accepts_same_bytes_and_rehashes(self):
        one = self.inputs()
        before = one.native_hash_file(self.artifact)
        one.assert_stable()
        self.hardlink_roundtrip(self.artifact)
        two = self.inputs()
        self.assertEqual(two.native_hash_file(self.artifact), before)
        self.assertEqual(two.native.hash_count, 1)
        two.assert_stable()
        self.assertNotIn(self.artifact, self.whole.files)

    def test_native_hardlink_during_interval_rejects(self):
        inputs = self.inputs()
        inputs.native_hash_file(self.artifact)
        self.hardlink_roundtrip(self.artifact)
        with self.assertRaises(InputDrift):
            inputs.assert_stable()

    def test_restored_native_bytes_during_interval_reject(self):
        inputs = self.inputs()
        before = inputs.native_hash_file(self.artifact)
        self.restored_write(self.artifact)
        self.assertEqual(file_hash(self.artifact), before)
        with self.assertRaises(InputDrift):
            inputs.native_hash_file(self.artifact)

    def test_source_restoration_across_intervals_rejects(self):
        one = self.inputs()
        one.hash_file(self.source)
        one.assert_stable()
        self.restored_write(self.source)
        with self.assertRaises(InputDrift):
            self.inputs().assert_stable()

    def test_optional_source_creation_and_removal_across_intervals_rejects(self):
        absent = self.root / 'lakefile.lean'
        self.inputs().optional_hash(absent)
        time.sleep(.002)
        absent.write_text('shadow\n')
        absent.unlink()
        with self.assertRaises(InputDrift):
            self.inputs().assert_stable()

    def test_changed_native_bytes_produce_new_binding(self):
        self.fixture()
        before = self.binding(self.inputs())
        self.artifact.write_bytes(b'different native output')
        after = self.binding(self.inputs())
        self.assertNotEqual(before, after)
        self.assertIn(self.source, self.whole.files)
        self.assertNotIn(self.artifact, self.whole.files)

    def test_native_metadata_between_bindings_preserves_compatibility(self):
        self.fixture()
        before = self.binding(self.inputs())
        self.hardlink_roundtrip(self.artifact)
        self.assertEqual(before, self.binding(self.inputs()))

    def test_exact_stamp_cache_reuses_hash_but_checks_path_components(self):
        one = self.inputs()
        expected = one.native_hash_file(self.artifact)
        two = self.inputs()
        with patch('lean_ci.state.file_hash', side_effect=AssertionError('should reuse exact stamp')):
            self.assertEqual(two.native_hash_file(self.artifact), expected)
        self.assertEqual(two.native.hash_count, 0)
        observed = list(two.native.components)
        self.assertIn(self.artifact, observed)
        original = self.root / 'original'
        target = self.root / 'target'
        target.write_bytes(b'fixed')
        original.symlink_to(target)
        guarded = self.inputs()
        guarded.native_hash_file(original)
        original.unlink(); original.symlink_to(target)
        with self.assertRaises(InputDrift):
            guarded.native_hash_file(original)

    def test_final_aggregate_observer_rejects_earlier_native_drift(self):
        other = self.artifact.with_name('Other.olean')
        other.write_bytes(b'other')
        final = self.inputs()
        final.native_hash_file(self.artifact)
        final.native_hash_file(other)
        self.hardlink_roundtrip(self.artifact)
        with self.assertRaises(InputDrift):
            final.assert_stable()

    def test_nested_pure_inspection_defers_scans_but_rejects_before_external_use(self):
        inputs = self.inputs()
        inputs.hash_file(self.source)
        inputs.native_hash_file(self.artifact)
        escaped = []
        with self.assertRaises(InputDrift):
            with inputs.inspection():
                with inputs.inspection():
                    self.restored_write(self.artifact)
                    inputs.assert_stable()
                inputs.assert_stable()
            escaped.append('binding consumed')
        self.assertEqual(escaped, [])
        self.assertEqual(inputs.native.scan_count, 2)
        self.assertEqual(self.whole.scan_count, 2)
        self.assertGreaterEqual(inputs.scan_seconds, 0)

    def test_progress_lookup_and_execution_preserve_native_temporal_guards(self):
        progress = Progress(self.root / 'progress')
        command = ['lean', 'Quartz.lean']
        receipt = {'state': 'completed', 'exit_code': 0, 'guard_failure': None,
                   'owned_group_gone': True, 'command': command}

        def binding(inputs):
            inputs.assert_stable()
            return {'arguments': command, 'native': inputs.native_hash_file(self.artifact)}

        first = self.inputs()
        progress.run(lambda: binding(first), lambda: (receipt, command))
        self.hardlink_roundtrip(self.artifact)
        second = self.inputs()
        reused = progress.run(lambda: binding(second), lambda: self.fail('must reuse'))
        self.assertEqual(reused['mode'], 'reused')
        third = self.inputs()
        original_lookup = progress.lookup

        def mutate_lookup(value):
            found = original_lookup(value)
            self.hardlink_roundtrip(self.artifact)
            return found

        with patch.object(progress, 'lookup', side_effect=mutate_lookup):
            with self.assertRaises(InputDrift):
                progress.run(lambda: binding(third), lambda: self.fail('must lookup'))
        fourth = self.inputs()

        def mutate_execute():
            self.restored_write(self.artifact)
            return receipt, command

        with self.assertRaises(InputDrift):
            progress.run(lambda: binding(fourth), mutate_execute, reuse=False)

    def test_namespace_redirection_restoration_inside_interval_rejects(self):
        target = self.root / 'target-namespace'
        target.mkdir()
        namespace = self.root / 'Quartz'
        namespace.symlink_to(target, target_is_directory=True)
        inputs = self.inputs()
        inputs.observe_resolution(namespace)
        self.restored_write(self.artifact)  # Advance the filesystem timestamps.
        namespace.unlink()
        namespace.symlink_to(target, target_is_directory=True)
        with self.assertRaises(InputDrift):
            inputs.assert_stable()

    def test_unrelated_namespace_entries_do_not_invalidate_resolution(self):
        namespace = self.root / 'Quartz'
        namespace.mkdir()
        inputs = self.inputs()
        inputs.observe_resolution(namespace)
        sibling = namespace / 'Unrelated.olean'
        sibling.write_bytes(b'unrelated cached module')
        inputs.assert_stable()
        sibling.unlink()
        inputs.assert_stable()

    def test_absent_namespace_still_detects_create_remove(self):
        namespace = self.root / 'Absent'
        inputs = self.inputs()
        inputs.observe_resolution(namespace)
        namespace.mkdir()
        namespace.rmdir()
        with self.assertRaises(InputDrift):
            inputs.assert_stable()

    def test_inspection_keeps_per_file_guards_eager(self):
        inputs = self.inputs()
        inputs.native_hash_file(self.artifact)
        with self.assertRaises(InputDrift):
            with inputs.inspection():
                self.restored_write(self.artifact)
                inputs.native_hash_file(self.artifact)

    def test_source_and_native_resolution_use_different_lifetimes(self):
        first = self.inputs()
        first.observe_resolution(self.artifact.parent / 'Absent')
        (self.artifact.parent / 'cache-entry').write_bytes(b'cache')
        with self.assertRaises(InputDrift):
            first.assert_stable()
        self.inputs().observe_resolution(self.artifact.parent / 'Absent')
        self.inputs().assert_stable()

    def test_reflection_routes_discovered_source_whole_and_rechecks_fresh_graph(self):
        library = self.fixture()
        toolchain = {'installation': str(self.root / 'compiler')}
        one = self.inputs()
        graph = ReflectionGraph(self.root, [str(library)], toolchain, observations=one)
        before = graph.node('Quartz')
        self.assertIn(self.source, self.whole.files)
        self.assertNotIn(self.artifact, self.whole.files)
        self.assertIn(self.artifact, one.native.files)
        self.artifact.write_bytes(b'new native output')
        two = self.inputs()
        changed = ReflectionGraph(self.root, [str(library)], toolchain, observations=two).node('Quartz')
        self.assertNotEqual(before, changed)
        self.restored_write(self.source)
        with self.assertRaises(InputDrift):
            self.inputs().assert_stable()

    def test_metadata_cache_uses_actual_hash_not_module_or_old_node(self):
        library = self.fixture()
        toolchain = {'installation': str(self.root / 'compiler')}
        one = self.inputs()
        ReflectionGraph(self.root, [str(library)], toolchain, observations=one).node('Quartz')
        metadata_path = library / 'Quartz.ilean'
        self.hardlink_roundtrip(metadata_path)
        two = self.inputs()
        with patch('lean_ci.state.read_json', wraps=lambda p: json.loads(Path(p).read_text())) as read:
            value = ReflectionGraph(self.root, [str(library)], toolchain, observations=two).node('Quartz')
        self.assertEqual(value['imports'], [])
        self.assertNotIn(metadata_path, [Path(call.args[0]) for call in read.call_args_list])
        write_json(metadata_path, {'version': 5, 'module': 'Quartz',
                                   'directImports': [['Other', False, False, False]]})
        three = self.inputs()
        value = ReflectionGraph(self.root, [str(library)], toolchain, observations=three).node('Quartz')
        self.assertEqual(value['imports'], ['Other'])
        self.assertEqual(len(self.metadata), 2)


if __name__ == '__main__':
    unittest.main()
