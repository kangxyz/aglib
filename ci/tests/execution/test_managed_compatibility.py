"""Canonical wrapper producer/configuration compatibility; no compiler runs."""
import hashlib
import json
from pathlib import Path
import shlex
import sys
import tempfile
import unittest

from lean_ci.execution.runtime import managed_mechanism
from lean_ci.execution.state import InputDrift, TemporalInputs


class ManagedCompatibility(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='managed-cache-key-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.physical = self.root / 'physical/bin/lean'
        self.physical.parent.mkdir(parents=True)
        self.physical.write_text('fixed physical compiler')
        self.sidecar = self.addressed('elastic', '# stable controller\n')
        self.worker = self.addressed('worker', 'ELASTIC_MODULE = ' + repr(self.sidecar.name) + '\n')

    def addressed(self, stem, text):
        digest = hashlib.sha256(text.encode()).hexdigest()
        path = self.root / (stem + '-' + digest + '.py')
        path.write_text(text)
        return path

    def overlay(self, label):
        run = self.root / label
        wrapper = run / 'toolchain/bin/lean'
        wrapper.parent.mkdir(parents=True)
        config = run / 'compiler-config.json'
        value = {'lean': str(self.physical), 'jobs': 8, 'threads': 4, 'heap_mib': 12800,
            'slots': str(run / 'slots'), 'events': str(run / 'compiler-events.jsonl'),
            'scope_fds': [13], 'scope_leases': [{'fd': 13, 'device': 1, 'inode': 2}],
            'scope_supervisor': {'pid': 100, 'start': 200, 'run_dir': str(run), 'workspace': '/same/workspace'},
            'admission': None, 'elastic': {'run_dir': str(run), 'workspace': '/same/workspace',
                                        'pool': {'directory': '/same/pool'}, 'limits': {'memory': 120}},
            'forbid_compilation': False}
        config.write_text(json.dumps(value))
        wrapper.write_text('#!/bin/sh\nexec ' + shlex.join([sys.executable, str(self.worker),
                                                          '__compiler__', str(config)]) + ' "$@"\n')
        profile = {'lean': str(wrapper), 'jobs': 8, 'threads': 4, 'lean_memory_mib': 12800}
        return profile, config

    def identity(self, profile, observer=None):
        return managed_mechanism(profile, self.physical, (observer or TemporalInputs()).hash_file)

    def test_coordinates_normalize_but_semantic_flags_and_producer_remain(self):
        first, _ = self.overlay('first')
        second, config = self.overlay('second')
        value = json.loads(config.read_text())
        value['scope_fds'] = [77]
        value['scope_leases'] = [{'fd': 77, 'device': 9, 'inode': 8}]
        value['scope_supervisor'].update(pid=999, start=888)
        config.write_text(json.dumps(value))
        old = self.identity(first)
        self.assertIsNotNone(old)
        self.assertEqual(self.identity(second), old)
        value['forbid_compilation'] = True
        config.write_text(json.dumps(value))
        self.assertNotEqual(self.identity(second), old)

    def test_unknown_wrapper_or_changed_worker_does_not_gain_normalization(self):
        profile, _ = self.overlay('first')
        wrapper = Path(profile['lean'])
        original = wrapper.read_text()
        wrapper.write_text(original.replace(' "$@"', ' -Dchanged=true "$@"'))
        self.assertIsNone(self.identity(profile))
        wrapper.write_text(original)
        self.worker.write_text(self.worker.read_text() + '# changed producer\n')
        self.assertIsNone(self.identity(profile))

    def test_new_content_addressed_worker_gets_a_distinct_semantic_key(self):
        first, _ = self.overlay('first')
        old = self.identity(first)
        self.worker = self.addressed('worker', 'ELASTIC_MODULE = ' + repr(self.sidecar.name) + '\n# new\n')
        second, _ = self.overlay('second')
        self.assertNotEqual(self.identity(second), old)

    def test_actual_configuration_stays_under_live_temporal_guard(self):
        profile, config = self.overlay('first')
        observer = TemporalInputs()
        self.assertIsNotNone(self.identity(profile, observer))
        original = config.read_bytes()
        config.write_bytes(original + b' ')
        config.write_bytes(original)
        with self.assertRaises(InputDrift):
            observer.assert_stable()


if __name__ == '__main__':
    unittest.main()
