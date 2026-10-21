#!/usr/bin/env python3
"""Execute Aglib's selected incremental build, lint and in-package tests."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote

from affected_scope import ROOT
from lean_ci.engine import Application
from lean_ci.resources import ResourceConfig
from lean_ci.runtime import NativeRuntime


def check_links(root, paths):
    for path in paths:
        file = root / path
        if file.suffix == '.json' and file.is_file():
            json.loads(file.read_text())
        if file.suffix != '.md' or not file.is_file():
            continue
        for target in re.findall(r'\]\(<?([^\s)>]+)>?(?:\s+[^)]*)?\)', file.read_text()):
            if target.startswith(('#', '/', 'http:', 'https:', 'mailto:', 'app:', 'plugin:')):
                continue
            local = unquote(target.split('#', 1)[0])
            if local and not (file.parent / local).exists():
                raise ValueError(f'Broken local Markdown link in {path}: {target}')


def execute(root, plan, directory, source_only=False, native_only=False, rehash=False,
            ci=False, outputs=None, phases=None, *, executor=None, toolchain=None):
    """Compatibility entry; shared execution always guards native work with --rehash."""
    from ci_pipeline import AglibLocalAdapter
    if outputs and phases and set(phases) != {'providers', 'provider-lint', 'consumers'}:
        raise ValueError('Export requires the complete selected validation, not a single-phase repair')
    adapter = AglibLocalAdapter(plan, source_only=source_only, native_only=native_only, phases=phases)
    config = ResourceConfig(prefix='AGLIB', profile_keys=('R5_LEAN_REMOTE_PROFILE',))
    application = Application(root, adapter, NativeRuntime(root, resource_config=config))
    return application.check(directory, progress=(directory / 'check-progress') if directory else None,
                             outputs=outputs, executor=executor, toolchain=toolchain)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base')
    parser.add_argument('--head')
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--plan', type=Path)
    parser.add_argument('--source-only', action='store_true')
    parser.add_argument('--native-only', action='store_true')
    parser.add_argument('--rehash', action='store_true')
    parser.add_argument('--ci', action='store_true')
    parser.add_argument('--outputs', type=Path)
    parser.add_argument('--phase', action='append', choices=['providers', 'provider-lint', 'consumers', 'trust', 'client'])
    args = parser.parse_args()
    try:
        if args.plan and (args.base or args.head or args.full):
            raise ValueError('Use either a guarded --plan or --base/--head')
        if args.source_only and args.native_only:
            raise ValueError('--source-only and --native-only are mutually exclusive')
        plan = json.loads(args.plan.read_text()) if args.plan else None
        directory = Path(os.environ['AGLIB_VERIFY_DIR']).resolve() if 'AGLIB_VERIFY_DIR' in os.environ else None
        if plan is not None:
            execute(ROOT, plan, directory, args.source_only, args.native_only,
                    args.rehash, args.ci, args.outputs, args.phase)
        else:
            from ci_pipeline import AglibLocalAdapter
            from lean_ci.engine import Application
            from lean_ci.resources import ResourceConfig
            from lean_ci.runtime import NativeRuntime
            if args.outputs and args.phase and set(args.phase) != {'providers', 'provider-lint', 'consumers'}:
                raise ValueError('Export requires complete selected validation')
            adapter = AglibLocalAdapter(head=args.head, full=args.full, source_only=args.source_only,
                                       native_only=args.native_only, phases=args.phase)
            config = ResourceConfig(prefix='AGLIB', profile_keys=('R5_LEAN_REMOTE_PROFILE',))
            Application(ROOT, adapter, NativeRuntime(ROOT, resource_config=config)).check(
                directory, requested_base=args.base, outputs=args.outputs)
        return 0
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print('Affected check failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
