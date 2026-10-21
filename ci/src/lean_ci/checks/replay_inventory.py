"""Configuration-owned exact replay inventory, distinct from ordinary CI checks."""
from dataclasses import dataclass
from functools import cached_property
import json
from pathlib import Path

from ..project.configuration import load_config
from ..project.source import module_name, module_path


@dataclass(frozen=True)
class ReplayInventory:
    repository: Path
    config: dict
    workspace: dict

    @property
    def root(self):
        return self.repository / self.workspace['path']

    @cached_property
    def rows(self):
        return {r['module']: r for r in self.config['modules'].values()
                if r['workspace'] == self.workspace['id']}

    def source(self, name):
        if name not in self.rows or self.rows[name]['role'] == 'expected_failure':
            raise RuntimeError('Unenrolled exact replay module: ' + name)
        return (self.repository / self.rows[name]['path']).relative_to(self.root)

    def included_support(self):
        paths = set()
        for name in self.config['policy']['inventory']:
            data = json.loads((self.repository / name).read_text())
            if data.get('schema') != 1 or data.get('kind') != 'inventory':
                raise ValueError('Unsupported replay inventory policy: ' + name)
            included = data.get('included_support', [])
            if not isinstance(included, list) or any(not isinstance(p, str) or not p for p in included):
                raise ValueError('Replay support inventory requires exact source paths')
            known = {r['path']: r for r in self.config['modules'].values()}
            if any(p not in known or known[p]['role'] in {'expected_failure', 'formal_only'} for p in included):
                raise ValueError('Replay support inventory cannot promote unknown, negative or formal-only sources')
            paths.update(included)
        return paths

    def expected_sources(self):
        support = self.included_support()
        return {self.source(n) for n, r in self.rows.items()
                if r['role'] in {'production', 'tests'} or r['path'] in support}

    def all_sources(self):
        sources = {(self.repository / r['path']).relative_to(self.root) for r in self.rows.values()}
        for value in self.config['formal_only']:
            path = self.repository / value
            if not path.is_relative_to(self.root):
                continue
            if any(w['id'] != self.workspace['id'] and w['path'] != '.'
                   and path.is_relative_to(self.repository / w['path']) for w in self.config['workspaces']):
                continue
            sources.add(path.relative_to(self.root))
        return sources

    def names(self, sources):
        by_path = {self.source(n): n for n, r in self.rows.items() if r['role'] != 'expected_failure'}
        if set(sources) - by_path.keys():
            raise RuntimeError('Replay source has no exact Lake module identity')
        return sorted(by_path[p] for p in sources)


def load_inventory(root, config_path='.github/lean-ci.toml', workspace=None):
    requested = Path(root).resolve()
    config_path = Path(config_path)
    candidates = [requested, *requested.parents]
    repository = next((p for p in candidates if (p / config_path).is_file()), None)
    if repository is None:
        raise ValueError('Replay requires the repository common CI configuration')
    relative = (repository / config_path).resolve().relative_to(repository).as_posix()
    config = load_config(repository, relative)
    matches = [w for w in config['workspaces'] if w['id'] == workspace] if workspace else [
        w for w in config['workspaces'] if (repository / w['path']).resolve() == requested]
    if not matches and workspace is None and requested == repository:
        matches = [config['workspaces'][0]]
    if len(matches) != 1:
        raise ValueError('Replay workspace must identify exactly one configured package')
    return ReplayInventory(repository, config, matches[0])


def expected_sources(root, client=False, *, inventory=None):
    return (inventory or load_inventory(root)).expected_sources()


def all_sources(root, *, inventory=None):
    return (inventory or load_inventory(root)).all_sources()


def check_inventory(root, modules=None, *, inventory=None):
    inventory = inventory or load_inventory(root)
    root = Path(root)
    library = root / '.lake/build/lib/lean'
    expected = set(inventory.names(inventory.expected_sources()))
    required = expected if modules is None else set(modules)
    for name in required:
        inventory.source(name)
    # Explicit formal/control probes have their own honest role; they do not
    # become positive proof enrollment merely by existing in the build tree.
    allowed = expected | required
    prefixes = {module_path(n).parts[0].removesuffix('.lean') for n in inventory.rows}
    identities = {module_path(n).with_suffix('.olean').as_posix(): n for n in inventory.rows}
    actual = {identities.get(p.relative_to(library).as_posix(), 'stale:' + p.relative_to(library).as_posix()) for p in library.rglob('*.olean')
              if p.relative_to(library).parts[0].removesuffix('.olean') in prefixes} if library.is_dir() else set()
    errors = []
    entries = {p.name: p for p in library.iterdir()} if library.is_dir() else {}
    for name in inventory.config['policy']['inventory']:
        data = json.loads((inventory.repository / name).read_text())
        for prefix in data.get('forbidden_prefixes', []):
            if prefix + '.olean' in entries or (prefix in entries and any(entries[prefix].rglob('*.olean'))):
                errors.append('Old project-prefix compiled artifacts remain: ' + prefix)
    if required - actual:
        errors.append('Missing compiled replay inventory: ' + ', '.join(sorted(required - actual)))
    if actual - allowed:
        errors.append('Stale or negative compiled replay inventory: ' + ', '.join(sorted(actual - allowed)))
    return errors
