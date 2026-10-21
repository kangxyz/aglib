#!/usr/bin/env python3
"""Transport native Lake staging directories through public pinned release assets.

Lake owns the hashes, mappings and staging format. A standard tar.gz is only
transport packaging. Normal current-source Lake builds decide artifact reuse.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tarfile
import tempfile
from urllib.error import HTTPError, URLError
from urllib.request import urlopen
import tomllib


def command(root, *args):
    return subprocess.check_output(args, cwd=root, text=True).strip()


def identity(root):
    return {
        'toolchain': (root / 'lean-toolchain').read_text().strip(),
        'compiler': command(root, 'lean', '--version'),
        'system': platform.system(),
        'arch': platform.machine(),
    }


def artifact_prefix(basis, revision):
    toolchain = re.sub(r'[^a-zA-Z0-9_.-]', '-', basis['toolchain'])
    return f"lake-native-v1-{basis['system']}-{basis['arch']}-{toolchain}-{revision}"


def asset_name(basis, revision):
    return artifact_prefix(basis, revision) + '.tar.gz'


def package_identity(selector):
    # Lake may print a simple hyphenated Name component with Lean quoting in a
    # manifest, while TOML uses the raw component. Only this unambiguous ASCII
    # case is decoded; dotted, nested-quoted and other Unicode names stay exact.
    if re.fullmatch(r'«[A-Za-z0-9_]+-[A-Za-z0-9_-]+»', selector):
        return selector[1:-1]
    return selector


def dependencies(root, repositories):
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        if package.get('type') != 'git' or package.get('inherited', False):
            continue
        match = re.fullmatch(r'https://github\.com/([^/]+/[^/]+?)(?:\.git)?/?',
                             package.get('url', ''))
        if match and match[1] in repositories:
            if not re.fullmatch(r'[0-9a-f]{40}', package['rev']):
                raise ValueError('Expected a resolved full Git revision in the manifest')
            selector = package['name']
            yield package_identity(selector), selector, match[1], package['rev']


def unpack(archive, destination):
    # Native stage directories are flat regular files. Refuse links, directories,
    # duplicate names and path traversal instead of trusting archive extraction.
    with tarfile.open(archive, 'r:gz') as stream:
        for member in stream:
            if not member.isfile() or Path(member.name).name != member.name:
                raise ValueError('Expected flat regular files in native cache transport')
            with stream.extractfile(member) as source, (destination / member.name).open('xb') as target:
                shutil.copyfileobj(source, target)


def public_asset(repository, basis, revision):
    return (f'https://github.com/{repository}/releases/download/cache-{revision}/'
            + asset_name(basis, revision))


def recent_candidates(repository, basis, configured_revision):
    # Bounded public lookup: at most 20 recent releases and 5 cache candidates.
    with urlopen(f'https://api.github.com/repos/{repository}/releases?per_page=20', timeout=30) as source:
        releases = json.load(source)
    candidates = []
    for release in releases[:20]:
        match = re.fullmatch(r'cache-([0-9a-f]{40})', release.get('tag_name', ''))
        if not match or release.get('draft') or not release.get('prerelease'):
            continue
        producer_revision = match[1]
        if producer_revision == configured_revision:
            continue
        if release.get('target_commitish') != producer_revision:
            continue
        expected_name = asset_name(basis, producer_revision)
        if any(asset['name'] == expected_name for asset in release.get('assets', [])):
            candidates.append((producer_revision, public_asset(repository, basis, producer_revision)))
        if len(candidates) == 5:
            break
    return candidates


def import_candidate(root, package, selector, repository, configured_revision, producer_revision, url, basis):
    with tempfile.TemporaryDirectory(prefix='lake-native-download-') as temporary:
        directory = Path(temporary)
        archive = directory / 'transport.tar.gz'
        # Public release assets require no cross-repository token.
        with urlopen(url, timeout=30) as source, archive.open('xb') as target:
            shutil.copyfileobj(source, target)
        staged = directory / 'staged'
        staged.mkdir()
        unpack(archive, staged)
        provenance = json.loads((staged / 'provenance.json').read_text())
        expected = dict(basis, package=package, repository=repository, revision=producer_revision)
        if provenance != expected:
            raise ValueError('incompatible producer artifact provenance')
        retained = validate_staged_groups(staged, package)
        subprocess.run(['lake', 'cache', 'unstage', str(staged), selector], cwd=root, check=True)
        if retained:
            print(f'{package}: retained {retained} client mapping groups; not registered '
                  'without an explicit matching workspace/package request', flush=True)
        print(f'{package}: imported producer {producer_revision} for configured pin '
              f'{configured_revision}; current Lake input checks decide reuse ({url})', flush=True)


CACHE_ERRORS = (OSError, ValueError, KeyError, EOFError, URLError, tarfile.TarError, subprocess.CalledProcessError)


def restore(root, repositories):
    basis = identity(root)
    for package, selector, repository, revision in dependencies(root, set(repositories)):
        try:
            import_candidate(root, package, selector, repository, revision, revision,
                             public_asset(repository, basis, revision), basis)
            continue
        except CACHE_ERRORS as error:
            print(f'{package}: exact-pin cache unavailable ({error}); checking recent cache seeds', flush=True)
        try:
            candidates = recent_candidates(repository, basis, revision)
        except CACHE_ERRORS as error:
            print(f'{package}: recent cache lookup unavailable ({error}); ordinary build fallback', flush=True)
            continue
        for producer_revision, url in candidates:
            try:
                import_candidate(root, package, selector, repository, revision, producer_revision, url, basis)
                break
            except CACHE_ERRORS as error:
                print(f'{package}: seed {producer_revision} unavailable ({error})', flush=True)
        else:
            # Acquisition is optional; the subsequent ordinary rehashed build
            # must run and keeps its normal failure semantics.
            print(f'{package}: no compatible cache seed; ordinary build fallback', flush=True)


def restore_pinned(root, repositories):
    """Restore exact pinned public assets; distinguish absence from failed access.

    Setup never turns a network, provenance or native import failure into a cold
    build. A genuinely unpublished asset (HTTP 404) is reported as unavailable;
    subsequent selected Lake cache probes still decide whether setup is ready.
    The reusable workflow's restore action owns its existing bounded seed policy.
    """
    basis, result = identity(root), []
    for package, selector, repository, revision in dependencies(root, set(repositories)):
        url = public_asset(repository, basis, revision)
        try:
            import_candidate(root, package, selector, repository, revision, revision, url, basis)
        except HTTPError as error:
            if error.code != 404:
                raise
            result.append({'package': package, 'revision': revision, 'status': 'not-published', 'url': url})
        else:
            result.append({'package': package, 'revision': revision, 'status': 'imported', 'url': url})
    return result



SUPPORTED_HEADER = '2026-03-17'
MAX_MAPPING_GROUPS = 64


def regular_file(path):
    path = Path(path)
    if path.is_symlink() or not path.is_file():
        raise ValueError('Expected a regular native cache file: ' + str(path))
    return path


def file_hash(path):
    return hashlib.sha256(regular_file(path).read_bytes()).hexdigest()


def output_artifacts(value):
    """Pinned Lake collectOutputDescrs semantics, restricted to safe flat names."""
    if value is None or isinstance(value, bool):
        return set()
    if isinstance(value, int) and 0 <= value < 2 ** 64:
        return {f'{value:016x}.art'}
    if isinstance(value, str):
        if re.fullmatch(r'[0-9a-fA-F]{16}(?:\.[A-Za-z0-9_.+-]*)?', value) is None:
            raise ValueError('Unsafe/invalid native artifact descriptor')
        name, dot, extension = value.partition('.')
        return {name.lower() + (dot + extension if extension else '')}
    if isinstance(value, (list, dict)):
        parts = value.values() if isinstance(value, dict) else value
        return set().union(*(output_artifacts(item) for item in parts))
    raise ValueError('Unsupported native output descriptor')


def read_mapping(path):
    """Validate native JSONL before Lake's deliberately permissive loader."""
    lines = regular_file(path).read_text().splitlines()
    if not lines or json.loads(lines[0]) != SUPPORTED_HEADER:
        raise ValueError('Unsupported native mapping header')
    entries = {}
    for line in lines[1:]:
        row = json.loads(line)
        if (not isinstance(row, list) or len(row) != 2 or not isinstance(row[0], str)
                or re.fullmatch('[0-9a-f]{16}', row[0]) is None):
            raise ValueError('Malformed native mapping row')
        key, value = row
        if key in entries and entries[key] != value:
            raise ValueError('Conflicting duplicate native mapping input: ' + key)
        output_artifacts(value)
        entries[key] = value
    return entries


def committed_coverage(summary, revision, *, required_owners=('engine.py', 'mappings.py', 'runtime.py', 'state.py')):
    """Recognize the committed CI finalizer, never a local/frozen completion.

    This checks the trusted producer's envelope; it does not authenticate a
    signature or independently replay the core's source/receipt acceptance.
    """
    if (not isinstance(summary, dict) or summary.get('schema') != 1
            or summary.get('status') != 'complete' or summary.get('head') != revision
            or 'source_basis' in summary
            or not isinstance(summary.get('plan_id'), str)
            or re.fullmatch('[0-9a-f]{64}', summary['plan_id']) is None
            or summary.get('required_phases') != ['source', 'native']
            or summary.get('performed_phases') != summary['required_phases']):
        raise ValueError('Coverage requires the completed committed CI finalizer envelope')
    implementation = summary.get('implementation')
    if (not isinstance(implementation, dict)
            or not set(required_owners) <= implementation.keys()
            or any(not isinstance(name, str) or Path(name).name != name
                   or not isinstance(value, str) or re.fullmatch('[0-9a-f]{64}', value) is None
                   for name, value in implementation.items())):
        raise ValueError('Coverage requires the committed CI implementation identity')
    for field in ('performed_checks', 'reused_checks', 'compiled_or_refreshed_targets',
                  'reused_build_targets'):
        if not isinstance(summary.get(field), list) or not all(
                isinstance(item, str) for item in summary[field]):
            raise ValueError('Coverage requires complete committed CI outcome fields')


def clean_publication_source(root):
    if command(root, 'git', 'status', '--porcelain', '--untracked-files=all'):
        raise ValueError('Committed CI publication requires a clean HEAD source checkout')


def mapping_groups(root, mappings, coverage, revision):
    """Admit only the exact side files exported by the trusted core finalizer.

    This is transport validation, not independent proof/receipt verification.
    The core's completed coverage remains the producer acceptance boundary.
    """
    root, mappings = root.resolve(), Path(mappings).absolute()
    if mappings.resolve() != mappings:
        raise ValueError('Mapping path must not contain symlink aliases')
    if coverage is None:
        read_mapping(mappings)
        if mappings.with_name(mappings.name + '.groups').exists():
            raise ValueError('Mapping side groups require their coverage summary')
        return [(root, mappings)]
    coverage = Path(coverage).absolute()
    if coverage != mappings.with_suffix(mappings.suffix + '.coverage.json'):
        raise ValueError('Expected the primary mapping coverage sidecar')
    summary = json.loads(regular_file(coverage).read_text())
    committed_coverage(summary, revision)
    clean_publication_source(root)
    groups = summary.get('mapping_groups')
    if not isinstance(groups, list) or not 1 <= len(groups) <= MAX_MAPPING_GROUPS:
        raise ValueError('Expected bounded complete mapping groups')
    repository = Path(command(root, 'git', 'rev-parse', '--show-toplevel')).resolve()
    side = mappings.with_name(mappings.name + '.groups')
    expected_sides, result, domains = set(), [], []
    toolchain = None
    for index, group in enumerate(groups):
        if not isinstance(group, dict):
            raise ValueError('Malformed mapping group')
        expected = mappings if index == 0 else side / f'{index:04d}.jsonl'
        if group.get('path') != str(expected) or group.get('primary') is not (index == 0):
            raise ValueError('Unexpected mapping group path/order')
        if not isinstance(group.get('sha256'), str) or group['sha256'] != file_hash(expected):
            raise ValueError('Missing/corrupt native mapping group')
        if expected.resolve() != expected:
            raise ValueError('Mapping group path must not contain symlink aliases')
        read_mapping(expected)
        domain = group.get('domain')
        if (not isinstance(domain, dict) or domain.get('format') != SUPPORTED_HEADER
                or domain.get('layout') != 'native-lake'
                or domain.get('platform') != [platform.system(), platform.machine()]
                or not isinstance(domain.get('workspace'), str)
                or not isinstance(domain.get('toolchain'), dict) or not domain['toolchain']):
            raise ValueError('Incompatible native mapping domain')
        cwd = Path(domain['workspace'])
        if (not cwd.is_absolute() or str(cwd.resolve()) != domain['workspace']
                or not cwd.is_dir() or not cwd.is_relative_to(repository)
                or (index == 0 and cwd != root)
                or not (cwd / 'lakefile.toml').is_file()):
            raise ValueError('Unexpected native producer workspace')
        if domain in domains:
            raise ValueError('Duplicate native mapping domain')
        domains.append(domain)
        if toolchain is None:
            toolchain = domain['toolchain']
        elif domain['toolchain'] != toolchain:
            raise ValueError('Incompatible native producer toolchains')
        if index:
            expected_sides.add(expected.name)
        result.append((cwd, expected))
    if side.is_symlink() or (side.exists() and not side.is_dir()):
        raise ValueError('Unexpected mapping side directory')
    actual_sides = {path.name for path in side.iterdir()} if side.exists() else set()
    if actual_sides != expected_sides:
        raise ValueError('Missing/unexpected native mapping side paths')
    return result


def producer_package(cwd):
    name = tomllib.loads(regular_file(cwd / 'lakefile.toml').read_text())['name']
    if not isinstance(name, str) or not name:
        raise ValueError('Expected a declared native producer package')
    return package_identity(name)


def mapping_artifacts(path):
    return set().union(*(output_artifacts(value) for value in read_mapping(path).values()))


def retained_coverage(staged, *, expected_hash=None, legacy=False):
    """Admit only the workflow's exact existing diagnostic coverage filename."""
    path = staged / 'validation-coverage.json'
    if not path.exists():
        return set()
    summary = json.loads(regular_file(path).read_text())
    provenance = json.loads(regular_file(staged / 'provenance.json').read_text())
    if legacy:
        # Historical core finalizers predate the extracted mappings.py owner.
        committed_coverage(summary, provenance['revision'],
                           required_owners=('engine.py', 'runtime.py', 'state.py'))
    else:
        committed_coverage(summary, provenance['revision'])
        if expected_hash is None or file_hash(path) != expected_hash:
            raise ValueError('Retained validation coverage differs from staged producer coverage')
    return {path.name}


def validate_staged_groups(staged, package):
    """Keep client namespaces in transport; only primary is registered remotely.

    The existing restore API selects one dependency package, not a producer's
    client workspace. Registering side maps there would change their namespace.
    """
    metadata = staged / 'mapping-groups.json'
    if not metadata.exists():
        # Original single-map public assets remain native-compatible.
        expected = (mapping_artifacts(staged / 'outputs.jsonl')
                    | {'outputs.jsonl', 'provenance.json'} | retained_coverage(staged, legacy=True))
        if {path.name for path in staged.iterdir()} != expected:
            raise ValueError('Missing/unexpected legacy native staging files')
        for name in expected:
            regular_file(staged / name)
        return 0
    document = json.loads(regular_file(metadata).read_text())
    if not isinstance(document, dict) or document.get('schema') != 1:
        raise ValueError('Invalid staged mapping group metadata')
    groups = document.get('groups')
    if not isinstance(groups, list) or not 1 <= len(groups) <= MAX_MAPPING_GROUPS:
        raise ValueError('Invalid staged mapping group count')
    expected = {'provenance.json', metadata.name} | retained_coverage(
        staged, expected_hash=document.get('coverage_sha256'))
    workspaces = set()
    for index, group in enumerate(groups):
        name = 'outputs.jsonl' if index == 0 else f'outputs.{index:04d}.jsonl'
        if (not isinstance(group, dict) or set(group) != {'mapping', 'sha256', 'package', 'workspace'}
                or group['mapping'] != name or not isinstance(group['package'], str)
                or not group['package'] or not isinstance(group['workspace'], str)):
            raise ValueError('Invalid staged mapping group identity')
        workspace = Path(group['workspace'])
        if (workspace.is_absolute() or '..' in workspace.parts
                or str(workspace) != group['workspace'] or group['workspace'] in workspaces):
            raise ValueError('Invalid staged relative producer workspace')
        workspaces.add(group['workspace'])
        if index == 0 and group['package'] != package:
            raise ValueError('Primary staged mapping package does not match provenance')
        path = staged / name
        if group['sha256'] != file_hash(path):
            raise ValueError('Corrupt staged mapping group')
        expected.add(name)
        expected.update(mapping_artifacts(path))
    if {path.name for path in staged.iterdir()} != expected:
        raise ValueError('Missing/unexpected staged native files')
    for name in expected:
        regular_file(staged / name)
    return len(groups) - 1


def stage(root, mappings, destination, repository, coverage=None):
    root, destination = root.resolve(), Path(destination).absolute()
    revision = command(root, 'git', 'rev-parse', 'HEAD')
    coverage_snapshot = file_hash(coverage) if coverage is not None else None
    groups = mapping_groups(root, mappings, coverage, revision)
    repository_root = Path(command(root, 'git', 'rev-parse', '--show-toplevel')).resolve()
    if (destination.resolve() != destination or destination.is_relative_to(repository_root)
            or (destination.exists() and (not destination.is_dir() or any(destination.iterdir())))):
        raise ValueError('Expected an empty external native staging destination')
    # Parse all producer identities before any native command or destination write.
    packages = [producer_package(cwd) for cwd, _ in groups]
    snapshots = [file_hash(path) for _, path in groups]
    configurations = [file_hash(cwd / 'lakefile.toml') for cwd, _ in groups]
    for cwd, _ in groups:
        relative = str((cwd / 'lakefile.toml').relative_to(repository_root))
        committed = command(repository_root, 'git', 'show', f'{revision}:{relative}')
        if committed != (cwd / 'lakefile.toml').read_text().strip():
            raise ValueError('Native producer package configuration differs from checked source')
    basis = identity(root)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='lake-native-groups-', dir=destination.parent) as temporary:
        directory = Path(temporary)
        combined = directory / 'combined'
        combined.mkdir()
        metadata = []
        for index, ((cwd, path), package, snapshot) in enumerate(zip(groups, packages, snapshots)):
            native = directory / f'{index:04d}'
            subprocess.run(['lake', 'cache', 'stage', str(path.resolve()), str(native)],
                           cwd=cwd, check=True)
            if file_hash(path) != snapshot or file_hash(native / 'outputs.jsonl') != snapshot:
                raise ValueError('Native mapping changed during staging')
            expected = mapping_artifacts(path) | {'outputs.jsonl'}
            if {item.name for item in native.iterdir()} != expected:
                raise ValueError('Missing/unexpected native staged files')
            output_name = 'outputs.jsonl' if index == 0 else f'outputs.{index:04d}.jsonl'
            for item in native.iterdir():
                regular_file(item)
                target = combined / (output_name if item.name == 'outputs.jsonl' else item.name)
                if target.exists():
                    if file_hash(target) != file_hash(item):
                        raise ValueError('Conflicting native staged artifact: ' + item.name)
                else:
                    shutil.copyfile(item, target)
            metadata.append({'mapping': output_name, 'sha256': snapshot, 'package': package,
                             'workspace': str(cwd.relative_to(repository_root))})
        provenance = dict(basis, package=packages[0], repository=repository, revision=revision)
        (combined / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
        if coverage is not None:
            (combined / 'mapping-groups.json').write_text(json.dumps(
                {'schema': 1, 'groups': metadata, 'coverage_sha256': coverage_snapshot}, indent=2) + '\n')
            validate_staged_groups(combined, packages[0])
        if (snapshots != [file_hash(path) for _, path in groups]
                or configurations != [file_hash(cwd / 'lakefile.toml') for cwd, _ in groups]):
            raise ValueError('Native producer input changed during staging')
        if coverage is not None:
            if file_hash(coverage) != coverage_snapshot:
                raise ValueError('Producer coverage changed during staging')
            clean_publication_source(root)
        if command(root, 'git', 'rev-parse', 'HEAD') != revision:
            raise ValueError('Checked source revision changed during staging')
        if destination.exists():
            destination.rmdir()
        combined.rename(destination)
    name = artifact_prefix(basis, revision) + '-' + os.environ.get('GITHUB_RUN_ID', 'local')
    name += '-' + os.environ.get('GITHUB_RUN_ATTEMPT', '1')
    if output := os.environ.get('GITHUB_OUTPUT'):
        with open(output, 'a') as stream:
            stream.write(f'artifact-name={name}\nartifact-path={destination.resolve()}\n')
    print(name)


def release(root, repository, revision, artifact):
    if not re.fullmatch(r'[0-9a-f]{40}', revision):
        raise ValueError('Release requires the full checked source revision')
    with tempfile.TemporaryDirectory(prefix='lake-native-release-') as temporary:
        directory = Path(temporary)
        staged = directory / 'staged'
        subprocess.run(['gh', 'run', 'download', os.environ['GITHUB_RUN_ID'], '--repo', repository,
                        '--name', artifact, '--dir', str(staged)], cwd=root, check=True)
        provenance = json.loads((staged / 'provenance.json').read_text())
        if provenance['repository'] != repository or provenance['revision'] != revision:
            raise ValueError('Staging artifact does not match the checked source revision')
        if ((staged / 'mapping-groups.json').exists()
                or (staged / 'validation-coverage.json').exists()):
            validate_staged_groups(staged, provenance['package'])
        archive = directory / asset_name(provenance, revision)
        with tarfile.open(archive, 'w:gz', compresslevel=1) as transport:
            for path in sorted(staged.iterdir()):
                if path.is_symlink() or not path.is_file():
                    raise ValueError('Expected native flat staging files')
                transport.add(path, arcname=path.name)
        tag = 'cache-' + revision
        view = ['gh', 'release', 'view', tag, '--repo', repository, '--json', 'assets',
                '--jq', '.assets[].name']
        try:
            existing = command(root, *view).splitlines()
        except subprocess.CalledProcessError:
            created = subprocess.run(['gh', 'release', 'create', tag, '--repo', repository,
                '--target', revision, '--prerelease', '--latest=false',
                '--title', 'Native Lake cache ' + revision,
                '--notes', 'Native Lake staging outputs from successful pinned CI checks.'], cwd=root)
            # Another platform producer may have created the same tag concurrently.
            if created.returncode:
                existing = command(root, *view).splitlines()
            else:
                existing = []
        if archive.name in existing:
            print(f'{tag}/{archive.name}: immutable cache asset already exists; preserving it')
            return
        subprocess.run(['gh', 'release', 'upload', tag, str(archive), '--repo', repository],
                       cwd=root, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    actions = parser.add_subparsers(dest='mode', required=True)
    download = actions.add_parser('restore')
    download.add_argument('--repositories', nargs='*', default=[])
    pinned = actions.add_parser('restore-pinned')
    pinned.add_argument('--repositories', nargs='*', default=[])
    upload = actions.add_parser('stage')
    upload.add_argument('--mappings', type=Path, required=True)
    upload.add_argument('--coverage', type=Path, help='Exact core mapping coverage sidecar')
    upload.add_argument('--destination', type=Path, required=True)
    upload.add_argument('--repository', required=True)
    publish = actions.add_parser('release')
    publish.add_argument('--repository', required=True)
    publish.add_argument('--revision', required=True)
    publish.add_argument('--artifact', required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    if args.mode == 'restore':
        restore(root, args.repositories)
    elif args.mode == 'restore-pinned':
        print(json.dumps(restore_pinned(root, args.repositories), sort_keys=True))
    elif args.mode == 'stage':
        stage(root, args.mappings, args.destination, args.repository, args.coverage)
    else:
        release(root, args.repository, args.revision, args.artifact)


if __name__ == '__main__':
    main()
