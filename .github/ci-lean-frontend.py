#!/usr/bin/env python3
"""Opt-in job-local Lean heap override with one compiler process at a time."""
import argparse
import fcntl
import json
import os
from pathlib import Path
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile


METADATA = {'--githash', '--version', '--short-version', '-v', '-V',
            '--print-prefix', '--print-libdir', '--help', '-h'}


def memory_args(arguments, memory_mib):
    """Replace only Lean's memory flags; preserve runtime/program arguments."""
    result, index = [], 0
    while index < len(arguments):
        argument = arguments[index]
        if argument in ('--', '--run', '-r'):
            return [*result, f'-M{memory_mib}', *arguments[index:]]
        if argument in ('-M', '--memory'):
            if index + 1 == len(arguments):
                raise ValueError(f'missing memory argument: {argument}')
            value = arguments[index + 1]
            if not value.isascii() or not value.isdecimal():
                raise ValueError(f'invalid memory argument for {argument}: {value!r}')
            index += 2
            continue
        if argument.startswith('--memory=') or (argument.startswith('-M') and len(argument) > 2):
            index += 1
            continue
        result.append(argument)
        index += 1
    return [*result, f'-M{memory_mib}']


def configure(memory_mib, aggregate_memory_mib=None, lean=None, runner_temp=None,
              github_env=None, github_path=None):
    # The reusable/hosted default neither requires Lean nor changes the environment.
    if memory_mib == 0:
        return {'enabled': False}
    if memory_mib < 0 or aggregate_memory_mib is None or memory_mib >= aggregate_memory_mib:
        raise ValueError('frontend memory must be positive and below the aggregate native limit')
    physical_mib = os.sysconf('SC_PHYS_PAGES') * os.sysconf('SC_PAGE_SIZE') // (1024 * 1024)
    effective_aggregate = min(aggregate_memory_mib, physical_mib - 2048)
    if memory_mib >= effective_aggregate:
        raise ValueError('frontend memory must be below the effective aggregate after the 2048 MiB runner reserve')
    if any(value is None for value in (lean, runner_temp, github_env, github_path)):
        raise ValueError('enabled frontend override requires Lean, runner temp and GitHub environment files')
    real_lean = Path(lean).resolve(strict=True)
    prefix = subprocess.run([str(real_lean), '--print-prefix'], check=True,
                            capture_output=True, text=True).stdout.strip()
    sysroot = Path(prefix).resolve(strict=True)
    if not (sysroot / 'lib/lean').is_dir() or not (sysroot / 'bin/lake').is_file():
        raise ValueError('Lean must have a complete pinned toolchain installation')
    runtime = Path(tempfile.mkdtemp(prefix='lean-ci-frontend-', dir=runner_temp))
    overlay = runtime / 'toolchain'
    (overlay / 'bin').mkdir(parents=True)
    for item in sysroot.iterdir():
        if item.name != 'bin':
            (overlay / item.name).symlink_to(item, target_is_directory=item.is_dir())
    for item in (sysroot / 'bin').iterdir():
        if item.name != 'lean':
            (overlay / 'bin' / item.name).symlink_to(item)

    lock = runtime / 'frontend.lock'
    descriptor = os.open(lock, os.O_RDWR | os.O_CREAT | os.O_EXCL, 0o600)
    identity = os.fstat(descriptor)
    os.close(descriptor)
    config = runtime / 'config.json'
    config.write_text(json.dumps({'lean': str(real_lean), 'memory_mib': memory_mib,
        'lock_identity': [identity.st_dev, identity.st_ino, identity.st_uid]}, indent=2) + '\n')
    config.chmod(0o600)
    helper = runtime / 'frontend.py'
    shutil.copyfile(Path(__file__).resolve(), helper)
    wrapper = overlay / 'bin/lean'
    command = [sys.executable, str(helper), 'run', str(config)]
    wrapper.write_text('#!/bin/sh\nexec ' + shlex.join(command) + ' "$@"\n')
    wrapper.chmod(0o700)
    environment = {'LEAN_SYSROOT': str(overlay), 'LEAN': str(wrapper), 'LAKE_OVERRIDE_LEAN': '1'}
    if any('\n' in value or '\r' in value for value in environment.values()):
        raise ValueError('frontend paths must fit GitHub single-line environment records')
    with Path(github_env).open('a') as stream:
        for name, value in environment.items():
            stream.write(f'{name}={value}\n')
    with Path(github_path).open('a') as stream:
        stream.write(str(overlay / 'bin') + '\n')
    return {'enabled': True, 'memory_mib': memory_mib, 'frontend_processes': 1,
            'effective_aggregate_mib': effective_aggregate,
            'runtime': str(runtime), 'environment': environment}


def run(config_path, arguments):
    config_path = Path(config_path)
    config = json.loads(config_path.read_text())
    real = config['lean']
    if len(arguments) == 1 and arguments[0] in METADATA:
        os.execv(real, [real, *arguments])
    effective = memory_args(arguments, config['memory_mib'])
    # A --run control program may itself launch Lake/Lean. Its compiler children
    # acquire the lock; holding it for the control program would deadlock them.
    for argument in arguments:
        if argument == '--':
            break
        if argument in ('--run', '-r'):
            os.execv(real, [real, *effective])
    # Never recreate/unlink the lock: that could admit a second compiler on a
    # different inode while the first still holds its inherited descriptor.
    descriptor = os.open(config_path.parent / 'frontend.lock', os.O_RDWR | os.O_NOFOLLOW)
    try:
        identity = os.fstat(descriptor)
        if (not stat.S_ISREG(identity.st_mode) or identity.st_nlink != 1
                or identity.st_uid != os.getuid()
                or [identity.st_dev, identity.st_ino, identity.st_uid] != config['lock_identity']):
            raise ValueError('frontend lock no longer belongs to this job configuration')
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        # Exec keeps the lock in the real compiler. Exit, SIGTERM and SIGKILL
        # release it through normal descriptor ownership, with no saved-PID kills.
        os.set_inheritable(descriptor, True)
        print(f"ci-lean-frontend: one compiler, effective -M{config['memory_mib']}",
              file=sys.stderr, flush=True)
        os.execv(real, [real, *effective])
    finally:
        os.close(descriptor)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_subparsers(dest='action', required=True)
    setup = actions.add_parser('configure')
    setup.add_argument('--memory-mib', type=int, default=0)
    setup.add_argument('--aggregate-memory-mib', type=int)
    setup.add_argument('--lean', type=Path)
    setup.add_argument('--runner-temp', type=Path)
    setup.add_argument('--github-env', type=Path)
    setup.add_argument('--github-path', type=Path)
    frontend = actions.add_parser('run')
    frontend.add_argument('config', type=Path)
    frontend.add_argument('arguments', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    try:
        if args.action == 'run':
            run(args.config, args.arguments)
        else:
            print(json.dumps(configure(args.memory_mib, args.aggregate_memory_mib, args.lean,
                                       args.runner_temp, args.github_env, args.github_path)))
        return 0
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f'Lean frontend configuration failed: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
