#!/usr/bin/env python3
"""Validate native root stages and selectively repack corrupt derived LTARs.

This validates transport bytes, not Lean proofs. Expanded compiled outputs are
never invalidated; native --no-build --rehash remains the applicability gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

MAP_SCHEMA = '2026-03-17'
CORRUPT = re.compile(r'bad \.ltar file|file is corrupted|removing corrupted file', re.I)


def sha(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def regular(path):
    if not path.is_file() or path.is_symlink():
        raise ValueError('expected regular native stage file: ' + str(path))


def read_map(path):
    regular(path)
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    if not rows or rows[0] != MAP_SCHEMA:
        raise ValueError('unsupported native mapping schema')
    archives, seen = {}, set()
    for row in rows[1:]:
        if not isinstance(row, list) or len(row) != 2 or not isinstance(row[0], str) or \
                not re.fullmatch('[0-9a-f]{16}', row[0]) or not isinstance(row[1], str) or \
                not re.fullmatch(r'[0-9a-f]{16}(?:\.[A-Za-z0-9._-]+)?', row[1]):
            raise ValueError('unsupported native root mapping entry')
        if row[0] in seen:
            raise ValueError('duplicate native input mapping')
        seen.add(row[0])
        if row[1].endswith('.ltar'):
            archives.setdefault(row[1], row[0])
    if not archives:
        raise ValueError('native root stage contains no LTAR module outputs')
    return archives


class Runner:
    def __init__(self, root, seconds=300, environment=None):
        self.root = root
        self.deadline = time.monotonic() + seconds
        self.commands = []
        self.environment = dict(os.environ if environment is None else environment)

    def run(self, argv, *, environment=None, stdin=None, check=True):
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError('native stage validation deadline expired')
        started = time.monotonic()
        process = subprocess.Popen(argv, cwd=self.root, env=environment or self.environment,
            stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            start_new_session=True)
        try:
            output, _ = process.communicate(stdin, timeout=remaining)
        except BaseException:
            try:
                os.killpg(process.pid, signal.SIGTERM)
                process.communicate(timeout=2)
            except (ProcessLookupError, subprocess.TimeoutExpired):
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.communicate()
            raise
        self.commands.append({'argv': list(map(str, argv)), 'exit': process.returncode,
                              'seconds': time.monotonic() - started})
        if output:
            print(output, end='' if output.endswith('\n') else '\n', flush=True)
        if check and process.returncode:
            raise ValueError('native stage command failed: ' + str(argv))
        return process.returncode, output


def validate(stage, leantar, runner, scratch):
    archives = read_map(stage / 'outputs.jsonl')
    scratch.mkdir()
    copied, inputs = {}, []
    for i, (name, dep_hash) in enumerate(archives.items()):
        original = stage / name
        regular(original)
        copy = scratch / name
        shutil.copyfile(original, copy)  # Never let leantar -r remove producer/store files.
        lib, ir = scratch / str(i) / 'lib', scratch / str(i) / 'ir'
        lib.mkdir(parents=True); ir.mkdir()
        copied[name] = copy
        inputs.append({'file': str(copy), 'base': [str(lib), str(ir)], 'hash': dep_hash})
    started = time.monotonic()
    code, output = runner.run([leantar, '--jobs', '2', '-f', '-r', '-x', '-j', '-'],
                             stdin=json.dumps(inputs), check=False)
    deleted = {name for name, path in copied.items() if not path.exists()}
    # A parse failure deleted only our disposable copy. IO/disk/other errors must
    # never be interpreted as permission to delete a producer's archive.
    lines = [line for line in output.splitlines() if line.strip()]
    reported, other = set(), []
    for line in lines:
        names = [name for name, path in copied.items() if line.startswith(str(path) + ':')]
        if len(names) == 1 and CORRUPT.search(line):
            reported.add(names[0])
        else:
            other.append(line)
    if other or deleted - reported or (code and not reported):
        raise ValueError('LTAR validation failed for a non-corruption/IO reason')
    # leantar0.1.20 -r returns0/deletes payload-corrupt inputs but returns1/keeps
    # invalid-magic inputs. Explicit per-copy diagnostics define both failures.
    bad = [name for name in archives if name in reported]
    temporary_files = [p for p in scratch.rglob('*') if p.is_file()]
    copied_paths = set(copied.values())
    result = {'archives': len(archives), 'compressed_bytes': sum((stage / n).stat().st_size for n in archives),
              'expanded_bytes': sum(p.stat().st_size for p in temporary_files if p not in copied_paths),
              'temporary_bytes': sum(p.stat().st_size for p in temporary_files),
              'seconds': time.monotonic() - started, 'bad_archives': bad}
    print(json.dumps({'ltar_validation': result}), flush=True)
    return result


def compiled_files(root, archive):
    relative = archive.relative_to(root / '.lake/build/ir').with_suffix('')
    library = root / '.lake/build/lib/lean' / relative
    ir = root / '.lake/build/ir' / relative
    return [Path(str(library) + suffix) for suffix in
            ('.olean', '.olean.server', '.olean.private', '.ilean', '.ir', '.ir.sig')] + \
           [Path(str(ir) + suffix) for suffix in ('.c', '.bc')]


def invalidate(root, native, stage, bad):
    identities = {name: ((stage / name).stat().st_size, sha(stage / name)) for name in bad}
    affected, compiled = [], {}
    ir_directory = root / '.lake/build/ir'
    if ir_directory.resolve() != ir_directory:
        raise ValueError('working archive scope is symlinked')
    for path in ir_directory.rglob('*.ltar'):
        regular(path)
        if path.resolve() != path:
            raise ValueError('working archive path is symlinked')
        if any(path.stat().st_size == size and sha(path) == fingerprint
               for size, fingerprint in identities.values()):
            affected.append(path)
            for file in compiled_files(root, path):
                if file.is_file():
                    regular(file)
                    compiled[str(file)] = sha(file)
    removed = []
    for path in affected:
        for derived in (path, Path(str(path) + '.hash')):
            if derived.exists():
                regular(derived); derived.unlink(); removed.append(str(derived))
    for name, (size, fingerprint) in identities.items():
        artifact = native / 'artifacts' / name
        if artifact.exists():
            regular(artifact)
            if artifact.resolve() != artifact:
                raise ValueError('native artifact-store path is symlinked')
            if artifact.stat().st_size != size or sha(artifact) != fingerprint:
                raise ValueError('bad artifact-store copy changed after staging')
            artifact.unlink(); removed.append(str(artifact))
    return removed, compiled


def metadata_guard(real, directory, environment=None):
    wrapper = directory / 'lean-metadata-only'
    wrapper.write_text('#!/usr/bin/env python3\nimport os,sys\na=sys.argv[1:]\n'
        'allowed={"--githash","--print-prefix","--version"}\n'
        'if sum(x in allowed for x in a)!=1 or any(x not in allowed and not '
        '(x.startswith("-j") or x.startswith("-M")) for x in a):\n'
        ' print("stage repair rejected Lean frontend",file=sys.stderr);sys.exit(94)\n'
        'os.execv(' + repr(real) + ',[' + repr(real) + ',*a])\n')
    wrapper.chmod(0o755)
    return dict(os.environ if environment is None else environment,
                LEAN=str(wrapper), LAKE_OVERRIDE_LEAN='true')


def prepare(args, runner, leantar, real_lean, scratch):
    if not args.build_target:
        raise ValueError('prepare requires the original production build targets')
    fresh = scratch / 'native-stage'
    runner.run(['lake', 'cache', 'stage', str(args.mapping), str(fresh)])
    first = validate(fresh, leantar, runner, scratch / 'first-validation')
    shutil.rmtree(scratch / 'first-validation')
    removed, compiled = [], {}
    if first['bad_archives']:
        removed, compiled = invalidate(args.root, args.native_cache, fresh, first['bad_archives'])
        mapping = scratch / 'fresh-repaired-mappings.jsonl'
        runner.run(['lake', '--no-build', '--rehash', 'build', *args.build_target, '-o', str(mapping)],
                   environment=metadata_guard(real_lean, scratch, runner.environment))
        if any(not Path(path).is_file() or sha(Path(path)) != fingerprint
               for path, fingerprint in compiled.items()):
            raise ValueError('selective derived repair changed compiled outputs')
        shutil.rmtree(fresh)
        runner.run(['lake', 'cache', 'stage', str(mapping), str(fresh)])
        final = validate(fresh, leantar, runner, scratch / 'second-validation')
        shutil.rmtree(scratch / 'second-validation')
        if final['bad_archives']:
            raise ValueError('native repack still produced corrupt archives')
    else:
        final = first
    if args.staging.exists():
        if args.staging.is_symlink():
            raise ValueError('staging destination is a symlink')
        for path in args.staging.iterdir():
            regular(path)
            if path.name not in ('outputs.jsonl', 'producer.json') and not re.fullmatch(
                    r'[0-9a-f]{16}(?:\.[A-Za-z0-9._-]+)?', path.name):
                raise ValueError('refusing to replace a non-native staging directory')
        shutil.rmtree(args.staging)
    shutil.move(str(fresh), args.staging)
    return {'first': first, 'final': final, 'removed_only_derived': removed,
            'compiled_sha256': compiled, 'compiled_bytes_unchanged': True}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    for name in ('prepare', 'verify'):
        p = sub.add_parser(name)
        p.add_argument('--root', type=Path, default=Path.cwd())
        p.add_argument('--staging', type=Path, required=True)
        p.add_argument('--native-cache', type=Path)
        p.add_argument('--report', type=Path)
        if name == 'prepare':
            p.add_argument('--mapping', type=Path, required=True)
            p.add_argument('--build-target', action='append', default=[])
    args = parser.parse_args(argv)
    args.root, args.staging = args.root.resolve(), args.staging.absolute()
    args.native_cache = (args.native_cache or Path(os.environ.get(
        'LAKE_CACHE_DIR', args.root / '.lake/native-cache'))).resolve()
    runner = Runner(args.root, environment=dict(os.environ, LAKE_CACHE_DIR=str(args.native_cache)))
    report = {'action': args.action, 'success': False}
    scratch = None
    try:
        if args.staging.is_symlink():
            raise ValueError('staging destination is a symlink')
        args.staging = args.staging.resolve()
        if args.staging == args.root or args.staging.is_relative_to(args.root) or args.root.is_relative_to(args.staging):
            raise ValueError('staging must be a separate owned directory outside the source checkout')
        if args.staging == args.native_cache or args.staging.is_relative_to(args.native_cache) or \
                args.native_cache.is_relative_to(args.staging):
            raise ValueError('staging must not overlap the native artifact store')
        _, version = runner.run(['lake', 'env', 'lean', '--version'])
        if not version.startswith('Lean (version 4.34.1,'):
            raise ValueError('stage helper requires pinned Lean4.34.1')
        _, prefix = runner.run(['lake', 'env', 'lean', '--print-prefix'])
        leantar = str(Path(prefix.strip()) / 'bin/leantar')
        real_lean = os.environ.get('LEAN') or str(Path(prefix.strip()) / 'bin/lean')
        args.staging.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='ltar-verify-', dir=args.staging.parent) as temporary:
            scratch = Path(temporary)
            if args.action == 'prepare':
                report.update(prepare(args, runner, leantar, real_lean, scratch))
            else:
                final = validate(args.staging, leantar, runner, scratch / 'validation')
                report['final'] = final
                if final['bad_archives']:
                    raise ValueError('downloaded native stage contains corrupt LTARs')
        report['success'] = True
        return 0
    except (OSError, ValueError, TimeoutError, subprocess.TimeoutExpired) as error:
        report['error'] = str(error)
        print('Stage failed: ' + str(error), file=sys.stderr)
        return 1
    finally:
        report['commands'] = runner.commands
        report['temporary_outputs_cleaned'] = scratch is None or not scratch.exists()
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    sys.exit(main())
