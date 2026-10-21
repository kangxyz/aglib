"""Data-only flat-package transport for selected common native checks.

The bundle records current source bytes and projection provenance. Its original
Git head is metadata, never proof that the dirty/transport snapshot is committed.
"""
import copy
import json
from pathlib import Path
import re
import subprocess
import tomllib

from ..project.configuration import load_config, safe_path
from ..application import implementation_identity
from ..project.scope import select_scope, snapshot
from ..execution.state import TemporalInputs, digest, file_hash, write_json

CONFIG = '.lean-ci/config.json'
PROJECTION = '.lean-ci/projection.json'
MANIFEST = '.native-inputs.json'
REQUEST = 'native-request.json'
PROFILE = 'canonical-origin-v1'
PINS = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
NATIVE_SCOPE_FIELDS = {'base', 'changed', 'requested_targets', 'auxiliary', 'providers', 'consumers', 'tests',
    'clients', 'modules', 'declarations', 'source_style', 'style', 'source_check', 'removed',
    'expected_failure', 'controls', 'common_controls', 'check_only', 'facades',
    'tooling', 'invalidations', 'native', 'initial', 'coverage'}
SOURCE_SCOPE_METADATA = {'baseline_enrollment', 'enrollment_changes', 'policy_changes'}


def _object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate transport JSON key: ' + key)
        result[key] = value
    return result


def read_data(path):
    path = Path(path)
    return json.loads(path.read_text(), object_pairs_hook=_object) if path.suffix == '.json' else tomllib.loads(path.read_text())


def _name(value, *, dot=False):
    from .frozen import relative_name
    if dot and value == '.':
        return value
    return relative_name(value).as_posix()


def _mapped(value, mapping):
    _name(value, dot=True)
    if value in mapping:
        return mapping[value]
    if mapping.get('.') == '.':
        return value
    candidates = [prefix for prefix in mapping if prefix != '.' and value.startswith(prefix + '/')]
    if not candidates:
        raise ValueError('No explicit native path projection for: ' + value)
    prefix = max(candidates, key=len)
    return (Path(mapping[prefix]) / value[len(prefix) + 1:]).as_posix()


def project_config(raw, mapping, policy_mapping, excluded):
    """Only typed repository-coordinate fields change; no source code is rendered."""
    value = copy.deepcopy(raw)
    value['package_dir'] = '.'
    for category, names in value.get('sources', {}).items():
        value['sources'][category] = [_mapped(p, mapping) for p in names if p not in excluded]
    for category in ('expected_failure', 'formal_only', 'controls'):
        if category in value:
            value[category] = [_mapped(p, mapping) for p in value[category]]
    for client in value.get('clients', []):
        client['path'] = _mapped(client['path'], mapping)
    value['policy'] = {kind: [policy_mapping[p] for p in names]
                       for kind, names in value.get('policy', {}).items()}
    return value


def project_policy(raw, category, mapping):
    """Project only the exact path fields consumed by the common typed policies."""
    value = copy.deepcopy(raw)
    if category == 'exceptions':
        for key in ('private_imports', 'import_exceptions', 'token_exceptions'):
            if key in value:
                value[key] = {_mapped(p, mapping): v for p, v in value[key].items()}
        if 'legacy_auditors' in value:
            value['legacy_auditors'] = [_mapped(p, mapping) for p in value['legacy_auditors']]
    elif category == 'budget' and value.get('schema_version') != 1:
        if 'legacy' in value:
            value['legacy'] = {_mapped(p, mapping): v for p, v in value['legacy'].items()}
    elif category == 'inventory':
        if 'included_support' in value:
            value['included_support'] = [_mapped(p, mapping) for p in value['included_support']]
    elif category == 'controls':
        if 'compile_pass' in value:
            value['compile_pass'] = [_mapped(p, mapping) for p in value['compile_pass']]
        for entry in value.get('expected_failures', []):
            entry['path'] = _mapped(entry['path'], mapping)
            entry['prerequisites'] = [_mapped(p, mapping) for p in entry.get('prerequisites', [])]
    # Captured heartbeat legacy keys are already package-relative. Declaration
    # nolints and style/native names are identifiers, not filesystem coordinates.
    # Dependency assessment paths stay original evidence; frozen execution never
    # re-runs Git dependency selection or imports those as native source paths.
    return value


def _regular(root, name):
    path = safe_path(root, _name(name), exists=True)
    for part in [path, *path.parents]:
        if part == root:
            break
        if part.is_symlink():
            raise ValueError('Native transport does not copy symlink inputs: ' + name)
    if not path.is_file():
        raise ValueError('Native transport requires a regular source input: ' + name)
    return path


def _git(root, *args):
    result = subprocess.run(['git', *args], cwd=root, capture_output=True, text=True)
    if result.returncode:
        raise ValueError('Native request needs its original Git selection inputs')
    return result.stdout.strip()



def project_scope(scope, mapping, package, modules):
    """Project current selectors; retain old-enrollment/policy diagnostics only at source.

    Module and qualified-client keys are identities. Extra source selectors are
    repository paths and follow the same explicit projection as their copied bytes.
    The original scope remains hash-bound in projection.json; it supplies no old
    source proof and is never recomputed against missing Git history remotely.
    """
    if (not isinstance(scope, dict) or set(scope) != NATIVE_SCOPE_FIELDS | SOURCE_SCOPE_METADATA
            or scope['baseline_enrollment'] not in {'present', 'absent'}
            or not isinstance(scope['enrollment_changes'], list)
            or not isinstance(scope['policy_changes'], dict)):
        raise ValueError('Unsupported original common scope fields/metadata')
    projected = {key: copy.deepcopy(value) for key, value in scope.items() if key in NATIVE_SCOPE_FIELDS}
    for key in ('expected_failure', 'controls'):
        projected[key] = [_mapped(p, mapping) for p in scope[key]]
    projected['source_check'] = [name if name in modules else _mapped(name, mapping)
                                 for name in scope['source_check']]
    prefix = Path(package)
    for key in ('changed', 'tooling'):
        projected[key] = [_mapped(p, mapping) for p in scope[key]
            if Path(p).is_relative_to(prefix)
            or any(p == n or p.startswith(n + '/') for n in mapping if n != '.')]
    return projected


def validate_scope(root, config, scope):
    """Validate admitted selection against current source, without hosted/Git claims."""
    if not isinstance(scope, dict):
        raise ValueError('Frozen common scope must be structured data')
    if set(scope) != NATIVE_SCOPE_FIELDS:
        raise ValueError('Unsupported frozen common scope fields')
    current = snapshot(root, config)
    def names(key, allowed):
        values = scope[key]
        if (not isinstance(values, list) or any(not isinstance(n, str) or n not in allowed for n in values)
                or len(set(values)) != len(values)):
            raise ValueError('Invalid current-source scope membership: ' + key)
        return set(values)
    for key in ('native', 'initial', 'common_controls'):
        if type(scope[key]) is not bool:
            raise ValueError('Frozen scope flags must be booleans')
    if scope['base'] is not None and (not isinstance(scope['base'], str) or re.fullmatch('[0-9a-f]{40}', scope['base']) is None):
        raise ValueError('Invalid original comparison metadata')
    if scope['coverage'] not in {'current-obligation-universe', 'explicit-targets', 'affected-import-closure'}:
        raise ValueError('Unsupported native selection coverage label')
    def eligible(roles, workspace='root'):
        return {n for n, row in current.items() if row['role'] in roles and row['workspace'] == workspace}
    providers = names('providers', eligible({'production'}))
    consumers = names('consumers', eligible({'production'}))
    tests = names('tests', eligible({'tests'}))
    auxiliary = names('auxiliary', eligible({'examples', 'diagnostics', 'support', 'formal_only'}))
    if providers & consumers:
        raise ValueError('Frozen provider/consumer groups overlap')
    clients = scope['clients']
    if not isinstance(clients, dict) or set(clients) != {w['id'] for w in config['clients']}:
        raise ValueError('Frozen client coordinates differ from configuration')
    built = providers | consumers | tests | auxiliary
    for identifier, values in clients.items():
        allowed = eligible({'production', 'tests'}, identifier)
        if (not isinstance(values, list) or any(not isinstance(n, str) or n not in allowed for n in values)
                or len(set(values)) != len(values)):
            raise ValueError('Invalid frozen client module membership')
        built.update(values)
    if names('modules', current) != built:
        raise ValueError('Frozen build groups differ from selected modules')
    if names('declarations', current) != {n for n in built if not current[n]['facade']}:
        raise ValueError('Frozen scope cannot omit required defining-origin checks')
    styles = names('source_style', {n for n, r in current.items() if r['role'] not in {'formal_only', 'control', 'expected_failure'}})
    if names('style', current) != styles:
        raise ValueError('Frozen source-style selections differ')
    source_keys = {name for name, row in current.items() if row['role'] != 'references'}
    source_keys.update(row['path'] for row in config['extra_sources'] if row['role'] != 'references')
    if not styles.issubset(names('source_check', source_keys)):
        raise ValueError('Frozen source checks cannot omit selected source-style origins')
    names('facades', {n for n, r in current.items() if r['facade']})
    names('expected_failure', set(config['expected_failure']))
    names('controls', set(config['controls']))
    checks = scope['check_only']
    if not isinstance(checks, dict) or set(checks) != {'declarations', 'builtin', 'axioms', 'inventory'}:
        raise ValueError('Invalid required native-check categories')
    for kind, values in checks.items():
        allowed = {n for n, row in current.items() if row['role'] in {'production', 'tests', 'examples', 'diagnostics'}} - built
        if kind == 'axioms':
            allowed = {n for n in allowed if current[n]['role'] != 'diagnostics'}
        if kind == 'declarations':
            allowed = {n for n in allowed if not current[n]['facade']}
        if (not isinstance(values, list) or any(not isinstance(n, str) or n not in allowed for n in values)
                or len(set(values)) != len(values)):
            raise ValueError('Invalid frozen check-only source membership')
    for key in ('changed', 'tooling'):
        if not isinstance(scope[key], list) or len(set(scope[key])) != len(scope[key]):
            raise ValueError('Invalid frozen changed-path metadata')
        for name in scope[key]:
            _name(name)
    for key in ('requested_targets', 'removed'):
        if not isinstance(scope[key], list) or any(not isinstance(n, str) for n in scope[key]):
            raise ValueError('Invalid frozen origin metadata')
    for target in scope['requested_targets']:
        name = target.removeprefix('+').removesuffix(':leanArts')
        if name not in current:
            raise ValueError('Frozen requested target is not a current source origin')
    if not isinstance(scope['invalidations'], list) or any(not isinstance(row, dict) for row in scope['invalidations']):
        raise ValueError('Invalid frozen invalidation metadata')
    native = bool(built or styles or scope['expected_failure'] or scope['controls']
                  or scope['common_controls'] or any(checks.values()))
    if scope['native'] != native or not native:
        raise ValueError('Frozen request has no matching native selection')


def create_request(root, config_path='.github/lean-ci.toml', requested_base=None, targets=(), *, bundle):
    root = Path(root).resolve(strict=True)
    if Path(_git(root, 'rev-parse', '--show-toplevel')).resolve() != root:
        raise ValueError('Request root must be the original Git repository root')
    head = _git(root, 'rev-parse', 'HEAD')
    config = load_config(root, str(config_path))
    raw = read_data(_regular(root, str(config_path)))
    package = config['package_dir']
    prefix = Path(package)
    mapping = {package: '.'}
    excluded = []
    # Sources explicitly enrolled outside a nested package get an owned transport
    # coordinate. External reference archives do not become native dependencies.
    for category, values in config['sources'].items():
        for name in values:
            if Path(name).is_relative_to(prefix):
                mapping[name] = Path(name).relative_to(prefix).as_posix()
            elif category == 'references':
                excluded.append(name)
            else:
                mapping[name] = '.lean-ci/sources/' + name
    for client in config['clients']:
        if not Path(client['path']).is_relative_to(prefix):
            raise ValueError('Client outside the flattened package requires a separately reviewed Lake path projection')
        mapping[client['path']] = Path(client['path']).relative_to(prefix).as_posix()
    def project(name):
        if Path(name).is_relative_to(prefix):
            return Path(name).relative_to(prefix).as_posix()
        return _mapped(name, mapping)
    # Record exact mappings for every copied source; mapper prefix entries cover
    # data fields that name directories rather than individual files.
    source_names = {row['path'] for row in config['modules'].values()}
    source_names.update(row['path'] for row in config['extra_sources']
                        if not any(row['path'] == p or row['path'].startswith(p + '/') for p in excluded))
    for name in source_names:
        mapping[name] = project(name)
    for workspace in config['workspaces']:
        for pin in (*PINS, 'scripts/nolints.json', 'scripts/nolints-style.txt'):
            name = (Path(workspace['path']) / pin).as_posix()
            if (root / name).is_file():
                source_names.add(name)
                mapping[name] = project(name)
        # Flattening preserves Lake source bytes, including relative local pins.
        # Every local target must therefore land at the same relative coordinate.
        for dependency in workspace['dependencies']:
            if 'path' in dependency:
                original = (root / workspace['path'] / dependency['path']).resolve()
                if not original.is_relative_to(root / package):
                    raise ValueError('Local Lake dependency escapes the flattened package')
                original_relative = original.relative_to(root).as_posix()
                projected = (Path(project(workspace['path'])) / dependency['path']).as_posix()
                if (Path('/transport') / projected).resolve() != (Path('/transport') / project(original_relative)).resolve():
                    raise ValueError('Local Lake dependency requires changing committed Lake source bytes')
    for name in PINS:
        _regular(root, (Path(package) / name).as_posix())
    observations = TemporalInputs()
    observations.hash_file(_regular(root, str(config_path)))
    for name in sorted(source_names):
        observations.hash_file(_regular(root, name))
    policy_names = sorted({p for values in config['policy'].values() for p in values})
    for name in policy_names:
        observations.hash_file(_regular(root, name))
    scope = select_scope(root, config, base=requested_base, targets=targets)
    if not scope['native']:
        raise ValueError('Frozen request has no matching native selection; source-only obligations remain separate')
    for workspace in config['clients']:
        if scope['clients'].get(workspace['id']) and not (root / workspace['path'] / 'lake-manifest.json').is_file():
            raise ValueError('Selected client requires its prepared pinned manifest before freezing: ' + workspace['id'])
    observations.assert_stable()
    destination = Path(bundle).absolute()
    if destination.resolve() != destination or destination.is_relative_to(root):
        raise ValueError('Native bundle must be an external canonical directory')
    if destination.exists():
        raise ValueError('Native bundle destination must not already exist')
    for parent in destination.parents:
        if parent.is_symlink() or (parent.exists() and not parent.is_dir()):
            raise ValueError('Native bundle parent is redirected or not a directory')
    destination.mkdir(parents=True)
    provenance = {}
    def copied(name, target):
        target = _name(target)
        if target in provenance:
            raise ValueError('Native path projection collision: ' + target)
        original = _regular(root, name)
        content = original.read_bytes()
        checksum = observations.hash_file(original)
        path = destination / target
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        if file_hash(path) != checksum:
            raise ValueError('Native source changed while copying: ' + name)
        provenance[target] = {'source': name, 'source_sha256': checksum, 'operation': 'copy'}
    for name in sorted(source_names):
        copied(name, mapping[name])
    original_config = '.lean-ci/originals/config' + Path(config_path).suffix
    copied(str(config_path), original_config)
    policy_mapping, policy_records = {}, []
    for index, name in enumerate(policy_names):
        categories = [kind for kind, names in config['policy'].items() if name in names]
        # One file cannot acquire two distinct typed projection interpretations.
        projected = [project_policy(read_data(root / name), kind, mapping) for kind in categories]
        if any(value != projected[0] for value in projected[1:]):
            raise ValueError('Policy data has conflicting native projection categories: ' + name)
        target = '.lean-ci/metadata/' + str(index) + '-' + Path(name).name
        original = '.lean-ci/originals/' + str(index) + '-' + Path(name).name
        copied(name, original)
        write_json(destination / target, projected[0])
        policy_mapping[name] = target
        policy_records.append({'source': name, 'original': original, 'projected': target,
                               'categories': categories})
    write_json(destination / CONFIG, project_config(raw, mapping, policy_mapping, set(excluded)))
    projected_config = load_config(destination, CONFIG)
    projected_scope = project_scope(scope, mapping, package, config['modules'])
    validate_scope(destination, projected_config, projected_scope)
    projection = {'schema': 1, 'kind': 'common-native-path-projection', 'git_head_metadata': head,
                  'repository_package': package, 'transport_package': '.', 'path_mapping': mapping,
                  'original_config': original_config, 'policy_mapping': policy_mapping,
                  'policies': policy_records, 'copies': provenance,
                  'excluded_references': sorted(excluded), 'original_scope': scope}
    write_json(destination / PROJECTION, projection)
    files = {p.relative_to(destination).as_posix(): file_hash(p) for p in destination.rglob('*') if p.is_file()}
    policy_inputs = sorted({CONFIG, PROJECTION, original_config, *policy_mapping.values(),
                            *(p['original'] for p in policy_records), MANIFEST})
    absent = []
    for workspace in projected_config['workspaces']:
        for pin in ('lakefile.lean', 'lake-manifest.json', 'scripts/nolints.json', 'scripts/nolints-style.txt'):
            name = (Path(workspace['path']) / pin).as_posix()
            if name not in files:
                absent.append(name)
    request = {'schema': 2, 'config': CONFIG, 'projection': PROJECTION, 'profile': PROFILE,
               'payload': {'scope': projected_scope, 'configuration': digest(projected_config)},
               'implementation': implementation_identity(), 'policy_inputs': policy_inputs,
               'coordinates': {'root': '.', 'package_cwd': '.',
                               'source_mapping': {'repository_package': package, 'transport_package': '.'}},
               'absent_inputs': sorted(set(absent))}
    write_json(destination / REQUEST, request)
    observations.assert_stable()
    if load_config(root, str(config_path)) != config or _git(root, 'rev-parse', 'HEAD') != head:
        raise ValueError('Native request source enrollment or original HEAD changed during projection')
    files[REQUEST] = file_hash(destination / REQUEST)
    write_json(destination / MANIFEST, {'schema': 1, 'files': files, 'content_sha256': digest(files),
        'git_head': head, 'source_basis': 'transport-snapshot; original Git head is metadata only',
        'projection': PROJECTION})
    outer_files = dict(files, **{MANIFEST: file_hash(destination / MANIFEST)})
    return {'bundle': str(destination), 'request': str(destination / REQUEST),
            'manifest': str(destination / MANIFEST), 'source_content_sha256': digest(outer_files),
            'git_head_metadata': head, 'profile': PROFILE,
            'sync_includes': sorted(outer_files), 'scope': projected_scope,
            'coverage': 'selected-native-request; no source/hosted-baseline closure'}


def load_request_application(root, package, request, manifest, admitted, observations):
    """Schema 2 factory: common installed code only, after structured admission."""
    from ..configured import ConfiguredAdapter
    from ..application import Application
    from .frozen import read_observed, source_path
    from ..execution.resources import ResourceConfig
    from ..execution.runtime import NativeRuntime
    root, package = Path(root), Path(package)
    if root != package or request['coordinates']['root'] != '.' or request['coordinates']['package_cwd'] != '.':
        raise ValueError('Config-native transport requires explicit flat root/package coordinates')
    if request.get('profile') != PROFILE or request.get('config') != CONFIG or request.get('projection') != PROJECTION:
        raise ValueError('Unsupported common native transport profile/configuration')
    def data(name):
        path = source_path(root, name)
        if path not in admitted:
            raise ValueError('Native configuration input is missing from SOURCE.files: ' + name)
        return read_observed(path, observations)
    transport = data(MANIFEST)
    source_files = dict(manifest['files'])
    source_files.pop(MANIFEST, None)
    if (transport.get('schema') != 1 or transport.get('files') != source_files
            or transport.get('content_sha256') != digest(source_files)):
        raise ValueError('Native input ownership manifest differs from admitted SOURCE')
    projection = data(PROJECTION)
    fields = {'schema', 'kind', 'git_head_metadata', 'repository_package', 'transport_package',
              'path_mapping', 'original_config', 'policy_mapping', 'policies', 'copies',
              'excluded_references', 'original_scope'}
    if (not isinstance(projection, dict) or set(projection) != fields or projection['schema'] != 1
            or projection['kind'] != 'common-native-path-projection' or projection['transport_package'] != '.'):
        raise ValueError('Unsupported native path projection metadata')
    original_package = _name(projection['repository_package'], dot=True)
    original_prefix = Path(original_package)
    if request['coordinates']['source_mapping'] != {'repository_package': original_package, 'transport_package': '.'}:
        raise ValueError('Native source mapping differs from projection metadata')
    original_path = source_path(root, projection['original_config'])
    if original_path not in admitted:
        raise ValueError('Original configuration data is not admitted')
    observations.hash_file(original_path)
    original = read_data(original_path)
    observations.hash_file(original_path)
    if original.get('package_dir', '.') != original_package or original.get('schema') != 1:
        raise ValueError('Original configuration/projected package mismatch')
    mapping = projection['path_mapping']
    if not isinstance(mapping, dict) or mapping.get(original_package) != '.':
        raise ValueError('Native source projection requires its explicit package mapping')
    external_sources = [p for kind, names in original.get('sources', {}).items()
                        if kind != 'references' for p in names if not Path(p).is_relative_to(original_prefix)]
    for source, target in mapping.items():
        _name(source, dot=True); _name(target, dot=True)
        expected = (Path(source).relative_to(original_prefix).as_posix()
                    if Path(source).is_relative_to(original_prefix) else '.lean-ci/sources/' + source)
        if target != expected or (not Path(source).is_relative_to(original_prefix)
                                 and not any(source == p or source.startswith(p + '/') for p in external_sources)):
            raise ValueError('Unapproved native path projection: ' + source)
    excluded = projection['excluded_references']
    expected_excluded = sorted(p for p in original.get('sources', {}).get('references', [])
                               if not Path(p).is_relative_to(original_prefix))
    if excluded != expected_excluded:
        raise ValueError('Excluded references differ from the explicit original source inventory')
    copies = projection['copies']
    if not isinstance(copies, dict):
        raise ValueError('Native copied-source provenance must be explicit')
    for name, record in copies.items():
        if (not isinstance(record, dict) or set(record) != {'source', 'source_sha256', 'operation'}
                or record['operation'] != 'copy'):
            raise ValueError('Invalid native copied-source provenance')
        _name(record['source'])
        path = source_path(root, name)
        if path not in admitted or observations.hash_file(path) != record['source_sha256']:
            raise ValueError('Copied native source bytes differ from their original input hash')
        if not name.startswith('.lean-ci/originals/') and _mapped(record['source'], mapping) != name:
            raise ValueError('Copied native source has an inconsistent path projection')
    policies = projection['policies']
    policy_mapping = projection['policy_mapping']
    source_policies = original.get('policy', {})
    expected_names = {p for names in source_policies.values() for p in names}
    if (not isinstance(policies, list) or not isinstance(policy_mapping, dict)
            or set(policy_mapping) != expected_names or len(policies) != len(expected_names)):
        raise ValueError('Projected policy inventory differs from original configuration')
    seen = set()
    for policy in policies:
        if not isinstance(policy, dict) or set(policy) != {'source', 'original', 'projected', 'categories'}:
            raise ValueError('Malformed typed native policy projection')
        source = policy['source']
        categories = [kind for kind, names in source_policies.items() if source in names]
        if (source in seen or source not in expected_names or policy['categories'] != categories
                or policy_mapping[source] != policy['projected']
                or copies.get(policy['original'], {}).get('source') != source):
            raise ValueError('Native typed policy source/category mismatch')
        seen.add(source)
        raw = data(policy['original'])
        projected = data(policy['projected'])
        if any(project_policy(raw, kind, mapping) != projected for kind in categories):
            raise ValueError('Projected native policy differs from its typed original data')
    if project_config(original, mapping, policy_mapping, set(excluded)) != data(CONFIG):
        raise ValueError('Projected configuration differs from its original typed data')
    config = load_config(root, CONFIG)
    if request['payload'].get('configuration') != digest(config) or set(request['payload']) != {'scope', 'configuration'}:
        raise ValueError('Frozen native payload configuration identity differs from admitted data')
    scope = request['payload']['scope']
    validate_scope(root, config, scope)
    original_scope = project_scope(projection['original_scope'], mapping, original_package, config['modules'])
    if original_scope != scope:
        raise ValueError('Frozen scope differs from its explicit original-coordinate selection')
    required = {CONFIG, PROJECTION, MANIFEST, projection['original_config'],
                *(p['original'] for p in policies), *policy_mapping.values()}
    required.update(row['path'] for row in config['modules'].values())
    required.update(row['path'] for row in config['extra_sources'])
    for workspace in config['workspaces']:
        for pin in (*PINS, 'lakefile.lean', 'scripts/nolints.json', 'scripts/nolints-style.txt'):
            name = (Path(workspace['path']) / pin).as_posix()
            if (root / name).exists():
                required.add(name)
            elif pin not in ('lean-toolchain', 'lakefile.toml') and name not in request.get('absent_inputs', []):
                raise ValueError('Optional native input absence is not explicit: ' + name)
    for name in required:
        if source_path(root, name) not in admitted:
            raise ValueError('Declared native source is not in SOURCE.files: ' + name)
    if not {CONFIG, PROJECTION, MANIFEST, projection['original_config'], *policy_mapping.values(),
            *(p['original'] for p in policies)}.issubset(set(request['policy_inputs'])):
        raise ValueError('Native data/policy inputs are not explicitly enrolled')
    runtime = NativeRuntime(root, resource_config=ResourceConfig(profile_keys=('R5_LEAN_REMOTE_PROFILE',)))
    return Application(root, ConfiguredAdapter(CONFIG, config=config), runtime=runtime, package_cwd=package)
