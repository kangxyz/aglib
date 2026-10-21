"""End-to-end synthetic interval/managed-identity regressions; no Lean runs."""
from copy import deepcopy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from lean_ci.engine import Application
from lean_ci.runtime import semantic_environment, semantic_toolchain
from lean_ci.state import InputDrift, TemporalInputs, check_binding, write_json
import test_engine as fixtures


class Policy:
    def tasks(self, root, plan, phase, directory):
        return [dict(id='search',kind='environment',command=['fixture-search'],cwd=str(root),
                     environment_output=str(directory/'search.txt'))] + [
            dict(id=name,kind='check',check_kind='fixture',command=['fixture-check',name],
                 cwd=str(root),modules=['Quartz.'+name]) for name in ('First','Second')]

    def binding(self, root, task, toolchain, reflection=None, observations=None):
        value=check_binding(root,'fixture',task['modules'],task['command'],['policy.py'],
             raw_paths=['Quartz/'+task['modules'][0].split('.')[-1]+'.lean'],toolchain=toolchain,
             hash_file=observations.hash_file)
        value['reflective_imports']=reflection.closure(task['modules']) if reflection else None
        return value


class ExecutionIntervals(unittest.TestCase):
    def setUp(self):
        self.temporary=tempfile.TemporaryDirectory(prefix='lean-check-intervals-')
        self.addCleanup(self.temporary.cleanup)
        self.scratch=Path(self.temporary.name).resolve()
        self.root=self.scratch/'root';(self.root/'Quartz').mkdir(parents=True)
        (self.root/'policy.py').write_text('# source policy\n')
        (self.root/'Init.lean').write_text('module\n')
        for name in ('First','Second'):
            (self.root/'Quartz'/ (name+'.lean')).write_text('module\ndef x := 1\n')
            fixtures.native_fixture(self.root,'Quartz.'+name)
        fixtures.native_fixture(self.root,'Init')
        self.application=Application(self.root,Policy())
        self.executor=fixtures.FixtureExecutor(self.root)
        self.directory=self.scratch/'run';self.directory.mkdir()
        self.observer=TemporalInputs()
        self.plan={'repository':str(self.root),'implementation':{'fixture':'owned'}}
        self.tasks=self.application._tasks(self.plan,'native',self.directory)
        self.artifact=self.root/'.lake/build/lib/lean/Quartz/First.ilean'

    def touch_metadata(self,path):
        link=self.scratch/'extra-link';os.link(path,link);link.unlink()

    def run_tasks(self):
        return self.application.run_tasks(self.plan,self.tasks,self.directory,
             self.scratch/'progress',fixtures.TOOLCHAIN,self.observer,self.executor)

    def test_cache_metadata_between_independent_checks_retains_valid_results(self):
        self.executor.callback=lambda task:self.touch_metadata(self.artifact) if task['id']=='Second' else None
        records=self.run_tasks()
        self.application.verify_tasks(self.plan,self.tasks,records,fixtures.TOOLCHAIN,self.observer)
        self.application.assert_verified_inputs(self.observer)
        self.assertEqual([r['id']for r in records],['search','First','Second'])
        self.assertLessEqual(self.application.execution_diagnostics()['operations']['binding']['calls'],6)

    def test_native_restore_during_consuming_check_cannot_save_success(self):
        self.executor.callback=lambda task:self.touch_metadata(self.artifact) if task['id']=='First' else None
        with self.assertRaises(InputDrift):self.run_tasks()
        self.assertFalse(list((self.scratch/'progress').glob('*.json')))

    def test_prior_source_restore_between_checks_remains_whole_attempt_drift(self):
        source=self.root/'Quartz/First.lean'
        def mutate(task):
            if task['id']=='Second':
                before=source.read_bytes();source.write_bytes(before+b' ');source.write_bytes(before)
        self.executor.callback=mutate
        with self.assertRaises(InputDrift):self.run_tasks()
        self.assertEqual(len(list((self.scratch/'progress').glob('*.json'))),1)

    def test_final_metadata_only_change_rehashes_one_native_file(self):
        records=self.run_tasks()
        self.application.verify_tasks(self.plan,self.tasks,records,fixtures.TOOLCHAIN,self.observer)
        self.touch_metadata(self.artifact)
        with patch('lean_ci.state.file_hash', wraps=fixtures.file_hash) as hashed:
            self.application.assert_verified_inputs(self.observer)
        self.assertEqual([Path(call.args[0]) for call in hashed.call_args_list],[self.artifact])

    def test_final_native_content_change_cannot_publish(self):
        records=self.run_tasks()
        self.application.verify_tasks(self.plan,self.tasks,records,fixtures.TOOLCHAIN,self.observer)
        content,before=self.artifact.read_bytes(),self.artifact.stat()
        self.artifact.write_bytes(bytes([content[0]^1])+content[1:])
        os.utime(self.artifact,ns=(before.st_atime_ns,before.st_mtime_ns))
        with self.assertRaises(InputDrift):self.application.assert_verified_inputs(self.observer)

    def test_binding_scan_cost_is_coalesced_and_reported(self):
        records=self.run_tasks()
        self.assertLessEqual(self.application.execution_diagnostics()['operations']['binding']['calls'],4)
        self.application.verify_tasks(self.plan,self.tasks,records,fixtures.TOOLCHAIN,self.observer)
        stats=self.application.execution_diagnostics()
        self.assertLessEqual(stats['operations']['binding']['calls'],6)
        self.assertGreater(stats['guards']['native_verification']['files'],0)
        self.assertGreaterEqual(stats['operations']['binding']['seconds'],0)

    def test_final_verification_reuses_hashes_and_parsed_imports(self):
        records=self.run_tasks()
        with patch('lean_ci.state.file_hash', side_effect=AssertionError('unchanged input rehashed')), \
             patch('lean_ci.state.read_json', wraps=fixtures.read_json) as read:
            self.application.verify_tasks(self.plan,self.tasks,records,fixtures.TOOLCHAIN,self.observer)
        self.assertFalse(any(str(call.args[0]).endswith('.ilean') for call in read.call_args_list))
        self.assertLessEqual(self.application.execution_diagnostics()['guards']['native_verification']['scans'],2)

    def test_changed_native_bytes_still_reject_preserved_success(self):
        records=self.run_tasks()
        self.artifact.write_text(self.artifact.read_text()+' ')
        with self.assertRaisesRegex(ValueError,'stale|corrupt'):
            self.application.verify_tasks(self.plan,self.tasks,records,fixtures.TOOLCHAIN,self.observer)

    def test_verification_scan_count_is_independent_of_receipt_count(self):
        original=self.tasks[-1]
        self.tasks=self.tasks[:1]+[dict(original,id='copy-'+str(i)) for i in range(24)]
        records=self.run_tasks()
        self.application.verify_tasks(self.plan,self.tasks,records,fixtures.TOOLCHAIN,self.observer)
        self.assertLessEqual(self.application.execution_diagnostics()['guards']['native_verification']['scans'],2)


class ManagedCacheIdentity(unittest.TestCase):
    def identity(self,name):
        wrapper='/runs/'+name+'/toolchain/bin/lean'
        profile={'schema_version':1,'jobs':8,'threads':4,'lean_memory_mib':12800,
                 'rss_limit_mib':110592,'lean':wrapper}
        return {'lean':'physical-compiler-sha','lake':'lake-sha','libleanshared.so':'runtime-sha',
            'installation':'/physical/compiler','managed_wrapper':'wrapper-'+name,'managed_profile':profile,
            'managed_mechanism':{'wrapper_template':'template-sha','worker_sha256':'worker-sha',
                                 'sidecar_sha256':'sidecar-sha','configuration':{'threads':4}},
            'resource_configuration':{'prefix':'QUARTZ','profile_keys':['R5_LEAN_REMOTE_PROFILE']},
            'execution_environment':{'LEAN':wrapper,'LEAN_SYSROOT':'/runs/'+name+'/toolchain',
                'PATH':'/runs/'+name+'/toolchain/bin:/stable/bin',
                'R5_LEAN_REMOTE_PROFILE':json.dumps(profile),'LEAN_OPTIONS':'-Dfixture=true'}}

    def test_new_owned_run_overlay_keeps_same_semantic_compiler_identity(self):
        first,second=self.identity('first'),self.identity('second')
        self.assertNotEqual(first,second)
        self.assertEqual(semantic_toolchain(first),semantic_toolchain(second))
        self.assertEqual(semantic_environment(first['execution_environment'],first),
                         semantic_environment(second['execution_environment'],second))

    def test_actual_compiler_options_and_other_search_path_still_invalidate(self):
        first=self.identity('first')
        for key,value in [('lean','different'),('libleanshared.so','different')]:
            other=deepcopy(first);other[key]=value
            self.assertNotEqual(semantic_toolchain(first),semantic_toolchain(other))
        for key,value in [('PATH','/other/bin'),('LEAN_OPTIONS','-Dfixture=false')]:
            other=deepcopy(first);other['execution_environment'][key]=value
            self.assertNotEqual(semantic_toolchain(first),semantic_toolchain(other))

    def test_changed_or_unknown_wrapper_producer_cannot_reuse(self):
        first=self.identity('first');second=self.identity('second')
        second['managed_mechanism']['worker_sha256']='different-worker'
        self.assertNotEqual(semantic_toolchain(first),semantic_toolchain(second))
        first.pop('managed_mechanism');second.pop('managed_mechanism')
        self.assertNotEqual(semantic_toolchain(first),semantic_toolchain(second))


if __name__=='__main__':unittest.main()
