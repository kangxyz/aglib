#!/usr/bin/env python3
"""Transport native Lake staging directories through public pinned release assets.

Lake owns the hashes, mappings and staging format. A standard tar.gz is only
transport packaging. Normal current-source Lake builds decide artifact reuse.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tarfile
import tempfile
from urllib.error import URLError
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
        subprocess.run(['lake', 'cache', 'unstage', str(staged), selector], cwd=root, check=True)
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


def stage(root, mappings, destination, repository):
    basis = identity(root)
    revision = command(root, 'git', 'rev-parse', 'HEAD')
    package = package_identity(tomllib.loads((root / 'lakefile.toml').read_text())['name'])
    subprocess.run(['lake', 'cache', 'stage', str(mappings.resolve()), str(destination.resolve())],
                   cwd=root, check=True)
    provenance = dict(basis, package=package, repository=repository, revision=revision)
    (destination / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
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
    upload = actions.add_parser('stage')
    upload.add_argument('--mappings', type=Path, required=True)
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
    elif args.mode == 'stage':
        stage(root, args.mappings, args.destination, args.repository)
    else:
        release(root, args.repository, args.revision, args.artifact)


if __name__ == '__main__':
    main()
