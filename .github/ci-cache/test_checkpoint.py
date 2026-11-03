"""Scoped checkpoint integrity, overlays and complete dependency recovery."""
from contextlib import redirect_stdout
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import stat
import tarfile
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('checkpoint', Path(__file__).with_name('checkpoint.py'))
checkpoint = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checkpoint)


class CheckpointTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / 'workspace'; self.root.mkdir()
        self.cache = self.base / 'native'; self.cache.mkdir()
        self.write('lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('lakefile.toml', 'name="Root"\n')
        self.write('lake-manifest.json', json.dumps({'packages': [
            {'name': 'dep', 'type': 'git', 'rev': 'fixed', 'url': 'https://example/dep'}]}))
        self.write('.lake/packages/dep/Dep.lean', 'SOURCE MUST NEVER CHANGE\n')

    def write(self, name, data, root=None):
        path = (root or self.root) / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(data)
        return path

    def invoke(self, *args, code=0):
        with redirect_stdout(io.StringIO()) as output:
            actual = checkpoint.main([*args, '--root', str(self.root), '--native-cache', str(self.cache)])
        self.assertEqual(actual, code)
        return json.loads(output.getvalue()) if actual == 0 else None

    def pack(self, layer):
        archive = self.base / (layer + '.tar')
        result = self.invoke('pack', '--layer', layer, '--output', str(archive))
        return archive, result

    def restore(self, layer, archive, code=0):
        return self.invoke('restore', '--layer', layer, '--input', str(archive), code=code)

    def test_root_is_complete_generated_scope_only_and_restore_breaks_hardlinks(self):
        source = self.write('Root.lean', 'PROOF SOURCE\n')
        artifact = self.write('.lake/build/lib/lean/Root.olean', 'compiled')
        test = self.write('.lake/build/ir/RootTest.c.o.export', 'test native')
        self.write('.lake/config/0/lakefile.olean', 'config')
        self.write('.lake/native-cache/artifacts/must-not-copy', 'global native store')
        os.chmod(artifact, 0o444)
        os.utime(artifact, ns=(1700000000123456789, 1700000000123456789))
        archive, result = self.pack('root')
        self.assertEqual(result['files'], 3)
        sibling = self.base / 'peer.olean'; os.link(artifact, sibling)
        artifact.unlink(); artifact.write_text('newer wrong bytes')
        self.restore('root', archive)
        self.assertEqual(artifact.read_text(), 'compiled')
        self.assertEqual(sibling.read_text(), 'compiled')
        self.assertNotEqual(artifact.stat().st_ino, sibling.stat().st_ino)
        self.assertEqual(stat.S_IMODE(artifact.stat().st_mode), 0o444)
        self.assertEqual(artifact.stat().st_mtime_ns, 1700000000123456789)
        self.assertEqual(test.read_text(), 'test native')
        self.assertEqual(source.read_text(), 'PROOF SOURCE\n')

    def test_complete_dependencies_include_prior_restored_outputs_and_generation_stable(self):
        path = self.write('.lake/packages/dep/.lake/build/lib/lean/Dep.olean', 'old unpublished')
        self.write('.lake/packages/dep/.git/config', 'private source checkout git metadata')
        archive, result = self.pack('dependencies')
        self.restore('dependencies', archive)
        stamp = archive.stat().st_mtime_ns
        _, same = self.pack('dependencies')
        self.assertFalse(same['changed'])
        self.assertTrue(same['reused_archive'])
        self.assertEqual(archive.stat().st_mtime_ns, stamp)
        os.utime(path, None)
        _, touched = self.pack('dependencies')
        self.assertFalse(touched['changed'])
        path.write_text('newly compiled')
        _, changed = self.pack('dependencies')
        self.assertTrue(changed['changed'])
        self.assertEqual(result['files'], 1)

    def test_tools_is_standalone_delta_against_current_build_not_prior_tool_cache(self):
        self.write('.lake/packages/dep/.lake/build/lib/lean/Dep.olean', 'base')
        dep_archive, _ = self.pack('dependencies')
        self.restore('dependencies', dep_archive)
        self.write('.lake/packages/dep/.lake/build/ir/Dep.c.o.export', 'old cached object')
        self.write('.lake/packages/dep/.lake/build/bin/checker', 'checker')
        self.write('.lake/build/lib/lean/RootTest.olean', 'root tests belong to root layer')
        self.write('.lake/lint-runner/BatchedLint.lean', 'generated private input')
        self.write('axiom-audit/.lake/build/bin/axiom-audit', 'auditor', self.cache)
        archive, data = self.pack('tools')
        self.assertEqual(data['files'], 4)
        self.restore('tools', archive)
        archive, again = self.pack('tools')
        self.assertEqual(again['files'], 4)  # Not a delta against the old tool cache.
        paths = [e['path'] for e in json.loads(Path(str(archive) + '.json').read_text())['entries']]
        self.assertFalse(any('RootTest' in p or p.endswith('Dep.olean') for p in paths))

    def test_context_change_rejects_before_overlay(self):
        path = self.write('.lake/build/lib/lean/Root.olean', 'old')
        archive, _ = self.pack('root')
        self.write('lean-toolchain', 'leanprover/lean4:changed\n')
        path.write_text('current')
        self.restore('root', archive, code=1)
        self.assertEqual(path.read_text(), 'current')

    def test_symlink_source_and_destination_are_rejected(self):
        outside = self.base / 'source.lean'; outside.write_text('SOURCE')
        path = self.root / '.lake/build/Root.olean'; path.parent.mkdir(parents=True)
        path.symlink_to(outside)
        self.invoke('pack', '--layer', 'root', '--output', str(self.base / 'bad.tar'), code=1)
        path.unlink(); path.write_text('valid compiled')
        archive, _ = self.pack('root')
        path.unlink(); path.symlink_to(outside)
        self.restore('root', archive, code=1)
        self.assertEqual(outside.read_text(), 'SOURCE')

    def rewrite(self, archive, transform):
        with tarfile.open(archive) as source:
            members = [(m, source.extractfile(m).read()) for m in source]
        transform(members)
        with tarfile.open(archive, 'w') as target:
            for member, data in members:
                member.size = len(data)
                target.addfile(member, io.BytesIO(data))

    def test_corrupt_extra_absolute_and_source_members_fail_without_partial_overlay(self):
        path = self.write('.lake/build/Root.olean', 'compiled')
        for attack in ('corrupt', 'extra', 'absolute', 'source', 'hardlink'):
            with self.subTest(attack=attack):
                path.write_text('compiled')
                archive, _ = self.pack('root')
                def transform(members):
                    if attack == 'corrupt':
                        members[1] = (members[1][0], b'changed!')
                    elif attack in ('extra', 'absolute'):
                        member = tarfile.TarInfo('/tmp/escape' if attack == 'absolute' else 'unexpected')
                        members.append((member, b'attack'))
                    elif attack == 'hardlink':
                        members[1][0].type = tarfile.LNKTYPE
                        members[1][0].linkname = '/tmp/escape'
                    else:
                        metadata = json.loads(members[0][1])
                        metadata['entries'][0]['path'] = 'Root.lean'
                        metadata['generation'] = checkpoint.digest([
                            checkpoint.semantic(e) for e in metadata['entries']])
                        members[0] = (members[0][0], json.dumps(metadata).encode())
                        members[1][0].name = 'payload/workspace/Root.lean'
                self.rewrite(archive, transform)
                path.write_text('current')
                self.restore('root', archive, code=1)
                self.assertEqual(path.read_text(), 'current')

    def test_external_dependency_is_not_silently_omitted(self):
        self.write('lake-manifest.json', json.dumps({'packages': [
            {'name': 'dep', 'type': 'path', 'dir': str(self.base / 'external')}]}))
        self.invoke('pack', '--layer', 'dependencies', '--output', str(self.base / 'bad.tar'), code=1)

    def test_only_lake_derived_setup_json_is_excluded_from_generation(self):
        self.write('.lake/build/ir/Root.setup.json', 'large disposable module setup')
        self.write('.lake/build/ir/keep.json', 'other JSON must remain')
        self.write('.lake/build/lib/lean/Root.olean', 'compiled')
        self.write('.lake/config/0/keep.setup.json', 'not a module compiler scaffold')
        root, data = self.pack('root')
        self.assertEqual(data['files'], 3)
        names = [e['path'] for e in json.loads(Path(str(root) + '.json').read_text())['entries']]
        self.assertNotIn('.lake/build/ir/Root.setup.json', names)
        self.assertIn('.lake/build/ir/keep.json', names)
        self.assertIn('.lake/config/0/keep.setup.json', names)
        setup = self.write('.lake/packages/dep/.lake/build/ir/Dep.setup.json', 'old setup')
        self.write('.lake/packages/dep/.lake/build/lib/lean/Dep.olean', 'compiled dep')
        archive, previous = self.pack('dependencies')
        self.assertEqual(previous['files'], 1)
        self.restore('dependencies', archive)
        setup.write_text('different regenerated scaffolding')
        _, current = self.pack('dependencies')
        self.assertFalse(current['changed'])
        self.assertTrue(current['reused_archive'])

    def test_mandatory_dependency_overlay_is_complete_after_optional_tool_cache(self):
        path = self.write('.lake/packages/dep/.lake/build/Dep.olean', 'CURRENT Build')
        archive, _ = self.pack('dependencies')
        path.write_text('old optional checkpoint')
        self.restore('dependencies', archive)
        self.assertEqual(path.read_text(), 'CURRENT Build')
        source = self.root / '.lake/packages/dep/Dep.lean'
        self.assertEqual(source.read_text(), 'SOURCE MUST NEVER CHANGE\n')


if __name__ == '__main__':
    unittest.main()
