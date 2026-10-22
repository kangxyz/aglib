#!/usr/bin/env python3
"""Build an incremental target graph under local or explicit managed resources."""
from contextlib import contextmanager
import json
import os
from pathlib import Path
import subprocess
import tempfile

from .source import MODULE
from .resources import limits, remote_profile, run


def build_threads(environment=None, config=None):
    environment = os.environ if environment is None else environment
    profile = remote_profile(environment, config)
    if profile is not None:
        return profile['threads']
    from .resources import ResourceConfig
    config = config or ResourceConfig()
    threads = int(config.value(environment, 'build_thread', '1'))
    available = os.cpu_count() or 1
    if not 1 <= threads <= available:
        raise ValueError('Build threads must be positive and not exceed available logical CPUs')
    return threads


@contextmanager
def capped_toolchain(root, threads=1, environment=None, config=None):
    environment = dict(os.environ if environment is None else environment)
    profile = remote_profile(environment, config)
    if profile is not None:
        # The parent wrapper already owns admission, compiler caps and source
        # identity. Selecting Elan here would silently bypass that wrapper.
        yield dict(environment, LEAN=profile['lean'], LAKE_OVERRIDE_LEAN='true',
                   LEAN_NUM_THREADS=str(profile['jobs']),
                   PATH=str(Path(profile['lean']).parent) + os.pathsep + environment.get('PATH', ''))
        return
    # Elan's read-only locator does not launch an unguarded Lean frontend.
    lean = subprocess.check_output(['elan', 'which', 'lean'], cwd=root, text=True, env=environment).strip()
    prefix = Path(lean).parent.parent
    budget = limits(environment, config=config)
    with tempfile.TemporaryDirectory(prefix='lean-ci-capped-toolchain-') as temporary:
        overlay = Path(temporary)
        for entry in prefix.iterdir():
            if entry.name != 'bin':
                (overlay / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
        (overlay / 'bin').mkdir()
        for entry in (prefix / 'bin').iterdir():
            if entry.name != 'lean':
                (overlay / 'bin' / entry.name).symlink_to(entry)
        wrapper = overlay / 'bin/lean'
        wrapper.write_text('#!/usr/bin/env python3\nimport os,sys\n'
            'args=[]; i=1\nwhile i<len(sys.argv):\n'
            ' a=sys.argv[i]\n'
            ' if a in ["-j","-M"]: i+=2; continue\n'
            ' if a.startswith("-j") or a.startswith("-M"): i+=1; continue\n'
            ' args.append(a); i+=1\n'
            'threads=1 if args in [["--githash"],["--print-prefix"],["--version"]] else '
            + repr(threads) + '\n'
            'os.environ["LEAN_NUM_THREADS"]=str(threads)\n'
            'os.execv(' + repr(lean) + ',[' + repr(lean) + ',"-j"+str(threads),'
            + repr('-M' + str(budget['lean_memory_mb'])) + ']+args)\n')
        wrapper.chmod(0o755)
        yield dict(environment, LEAN_SYSROOT=str(overlay), LEAN=str(wrapper),
                   LAKE_OVERRIDE_LEAN='true', LEAN_NUM_THREADS='1',
                   PATH=str(overlay / 'bin') + os.pathsep + environment.get('PATH', ''))


def native_targets(targets, selection='module'):
    """Render Lake selectors only here; callers and source queries use bare names."""
    if selection not in ('module', 'library'):
        raise ValueError('Build selection must be module or library')
    names = list(targets)
    for name in names:
        if not isinstance(name, str) or MODULE.fullmatch(name) is None:
            raise ValueError('Expected a bare Lean target name: ' + str(name))
    return [('+' + name) if selection == 'module' else name for name in names]


def build(root, targets, directory, rehash=False, outputs=None, *, environment=None, config=None, selection='module'):
    selectors = native_targets(targets, selection)
    directory.mkdir(parents=True, exist_ok=True)
    receipt = directory / 'graph-build.json'
    # Reserve this invocation's receipt before setup or launch. Native Lake owns
    # dependency scheduling and cache decisions; no preliminary build is needed.
    with receipt.open('x') as reserved:
        json.dump({'state': 'reserved'}, reserved)
    lake = ['lake'] + (['--rehash'] if rehash else [])
    output_args = ['-o', str(outputs.resolve())] if outputs is not None else []
    if outputs is not None:
        outputs.parent.mkdir(parents=True, exist_ok=True)
    budget = limits(environment, config=config)
    budget['native_build_threads'] = build_threads(environment, config)
    with capped_toolchain(root, threads=budget['native_build_threads'], environment=environment, config=config) as env:
        return run(lake + ['build', *selectors, *output_args], cwd=root, env=env,
                   receipt=receipt, budget=budget, config=config)
