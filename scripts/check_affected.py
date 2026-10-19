#!/usr/bin/env python3
"""Execute Aglib's selected final checks: providers, lint, consumers, trust, client."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from urllib.parse import unquote

from affected_scope import ROOT, select, validate
from library_sources import lean_imports, module_path


def run(root, command):
    print('+ ' + ' '.join(map(str, command)), flush=True)
    subprocess.run(list(map(str, command)), cwd=root, check=True)


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
            ci=False, outputs=None, phases=None):
    validate(root, plan)
    phases = set(phases or ['providers', 'provider-lint', 'consumers', 'trust', 'client'])
    if not native_only:
        for script in ['generate_imports.py', 'check_library_layout.py',
                       'check_placeholders.py', 'check_source_policy.py']:
            run(root, ['python3', 'scripts/' + script] + (['--check'] if script == 'generate_imports.py' else []))
        check_links(root, plan['changed'])
        for test in plan['tooling_tests']:
            if test == 'native-cache':
                run(root, ['python3', '-m', 'unittest', 'discover', '-s', '.github/actions/lake-cache', '-p', 'test_*.py'])
            else:
                run(root, ['python3', '-m', 'unittest', 'discover', '-s', 'scripts', '-p', test + '.py'])
    if source_only or not plan['native']:
        print('Static/source coverage only; no Lean, native cache or cache publication required.')
        return
    directory.mkdir(parents=True, exist_ok=True)
    mappings = []
    audit_targets = []
    lake = ['lake'] + (['--rehash'] if rehash else [])
    env = os.environ
    env['LEAN_NUM_THREADS'] = '1'

    def safe(phase, command, cwd=root):
        run(cwd, ['python3', root / 'scripts/resource_guard.py', '--capped-toolchain',
                  '--receipt', directory / (phase + '.json'), '--', *command])

    def build(phase, names, cwd=root):
        if not names:
            return
        facades = {n.removeprefix('client:') for n in plan['facades']
                   if n.startswith('client:') == (cwd != root)}
        # Import-only consumers may be very broad. Never fill their unrelated cold
        # imports by accident: recover the matching cache, then retry this phase.
        unrelated = set()
        for target in set(names) & facades:
            key = ('client:' if cwd != root else '') + target
            unrelated.update(n.removeprefix('client:') for n in plan['imports'][key]
                             if n.removeprefix('client:') not in names)
        if unrelated:
            safe(phase + '-cached-imports', lake + ['--no-build', 'build', *sorted(unrelated)], cwd)
        mapping = directory / (phase + '-outputs.jsonl')
        command = ['python3', root / 'scripts/build_serial.py', '--receipt-dir',
                   directory / phase] + (['--rehash'] if rehash else [])
        if cwd == root:
            command += ['--outputs', mapping]
            mappings.append(mapping)
        run(cwd, command + names)

    def lint(phase, names, styles=None):
        nonlocal runtime_prepared
        if ci and not runtime_prepared and (names or styles):
            modules = set()
            for driver in ['.lake/packages/batteries/scripts/runLinter.lean',
                           '.lake/packages/mathlib/scripts/lint-style.lean']:
                modules.update(n for n in lean_imports((root / driver).read_text())
                               if n.startswith(('Batteries.', 'Mathlib.', 'Cli.', 'ImportGraph.')))
            if modules:
                safe(phase + '-linter-runtime', lake + ['build', *('+' + n for n in sorted(modules))])
            runtime_prepared = True
        if names:
            safe(phase + '-builtin', lake + ['--no-build', 'lint', '--builtin-only', *names])
            safe(phase + '-declarations', ['python3', 'scripts/run_declaration_linter.py', *names])
        if styles:
            safe(phase + '-style', ['python3', 'scripts/run_style_linter.py', '--modules', *styles])

    runtime_prepared = False
    if 'providers' in phases:
        build('providers', plan['providers'])
    if 'provider-lint' in phases:
        lint('providers', plan['providers'], plan['providers'])
    if 'consumers' in phases:
        # Build implementations before import-only facades; test roots follow tests.
        build('consumers', plan['consumers'])
        build('tests', plan['tests'])
        rest = sorted(set(plan['style']) - set(plan['providers']))
        lint('consumers', [n for n in plan['consumers'] + plan['tests'] if n not in plan['facades']], rest)
    if 'trust' in phases and plan['trust']:
        audit_targets = ['AglibTest.AuditSupport']
        if 'AglibTest.AuditCoverage' not in plan['tests']:
            audit_targets.append('AglibTest.AuditCoverage')
        build('audit-support', audit_targets)
        if 'AglibTest/AuditSupport.lean' in plan['changed']:
            lint('audit-support', ['AglibTest.AuditSupport'])
        selected = [n for n in plan['providers'] + plan['consumers'] + plan['tests'] if n not in plan['facades']]
        if 'AglibTest/AuditSupport.lean' in plan['changed']:
            selected.append('AglibTest.AuditSupport')
        # Reuse the maintained origin auditor, including private/generated names.
        # No production root is imported just to discover its unrelated modules.
        audit = directory / 'SelectedAudit.lean'
        legacy = (root / 'AglibTest/Axioms.lean').read_text()
        start = legacy.index('  let env ← getEnv\n')
        end = legacy.index('  logInfo m!"Audited ', start)
        origin_controls = legacy[start:end]
        audit.write_text('import AglibTest.AuditSupport\nimport AglibTest.AuditCoverage\n'
                         + ''.join('import ' + n + '\n' for n in selected if n not in {'AglibTest.AuditSupport', 'AglibTest.AuditCoverage'})
                         + '\nopen Lean in\nrun_cmd do\n'
                         + '  let count ← AglibAudit.auditModules #['
                         + ', '.join('`' + n for n in selected) + ']\n'
                         + origin_controls
                         + '  logInfo m!"Selected-origin axiom audit: {count} declarations; '
                         + 'private/generated origin control: {coverageCount}."\n')
        safe('axioms', ['lake', 'env', 'lean', '-j1', audit])
        if 'AglibTest/Axioms.lean' in plan['changed']:
            safe('legacy-audit-cached-imports', lake + ['--no-build', 'build',
                 'Aglib', 'AglibTest.AuditSupport', 'AglibTest.AuditCoverage'])
            safe('legacy-audit-source', ['lake', 'env', 'lean', '-j1', 'AglibTest/Axioms.lean'])
        safe('negative-controls', ['python3', 'scripts/check_negative_controls.py'])
        required = [*plan['providers'], *plan['consumers'], *plan['tests'], *audit_targets]
        run(root, ['python3', 'scripts/check_compiled_inventory.py', '--modules', *required])
        if not ci and selected:
            run(root, ['python3', 'scripts/check_kernel.py', '--receipt-dir', directory / 'kernel', '--modules', *selected])
    if 'client' in phases and plan['client_audit']:
        run(root, ['python3', 'scripts/prepare_downstream.py'])
        client = root / 'examples/downstream'
        build('client', plan['client'], client)
        # The existing independent audit requires Consumer. Its imports must be
        # cached before that aggregate is built, just like other broad facades.
        safe('client-cached-audit-import', lake + ['--no-build', 'build', 'Consumer'], client)
        safe('client-audit', ['lake', 'env', 'lean', '-j1', 'Audit.lean'], client)
        if not ci and plan['client']:
            run(root, ['python3', 'scripts/check_kernel.py', '--root', client, '--client',
                       '--receipt-dir', directory / 'client-kernel', '--modules', *plan['client']])
    validate(root, plan)
    if outputs and mappings:
        if phases != {'providers', 'provider-lint', 'consumers', 'trust', 'client'}:
            raise ValueError('Export requires the complete selected validation, not a single-phase repair')
        # Consume successful build mappings; export never schedules another build.
        outputs.parent.mkdir(parents=True, exist_ok=True)
        with outputs.open('x') as stream:
            for mapping in mappings:
                stream.write(mapping.read_text())
        outputs.with_suffix(outputs.suffix + '.coverage.json').write_text(json.dumps({
            'coverage': plan['coverage'], 'base': plan['base'], 'head': plan['head'],
            'selected_targets': plan['providers'] + plan['consumers'] + plan['tests']
                                + audit_targets,
            'independent_replay': 'selected-modules' if not ci else 'retained-evidence-required',
        }, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base')
    parser.add_argument('--head')
    parser.add_argument('--plan', type=Path)
    parser.add_argument('--source-only', action='store_true')
    parser.add_argument('--native-only', action='store_true')
    parser.add_argument('--rehash', action='store_true')
    parser.add_argument('--ci', action='store_true')
    parser.add_argument('--outputs', type=Path)
    parser.add_argument('--phase', action='append', choices=['providers', 'provider-lint', 'consumers', 'trust', 'client'])
    args = parser.parse_args()
    try:
        if args.plan and (args.base or args.head):
            raise ValueError('Use either a guarded --plan or --base/--head')
        if args.source_only and args.native_only:
            raise ValueError('--source-only and --native-only are mutually exclusive')
        plan = json.loads(args.plan.read_text()) if args.plan else select(ROOT, args.base, args.head)
        directory = Path(os.environ['AGLIB_VERIFY_DIR']).resolve() if 'AGLIB_VERIFY_DIR' in os.environ else None
        if directory is None and plan['native'] and not args.source_only:
            directory = Path(tempfile.mkdtemp(prefix='aglib-affected-'))
        execute(ROOT, plan, directory, args.source_only, args.native_only,
                args.rehash, args.ci, args.outputs, args.phase)
        return 0
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print('Affected check failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
