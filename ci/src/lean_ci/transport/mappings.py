"""Validate and export successful native Lake mapping groups without compiling."""
import json
import platform
from pathlib import Path
import re

from ..execution.state import digest, file_hash, valid_receipt


SUPPORTED_HEADER = '2026-03-17'


def read_mapping(path):
    lines = Path(path).read_text().splitlines()
    if not lines or json.loads(lines[0]) != SUPPORTED_HEADER:
        raise ValueError('Unsupported native mapping header: ' + str(path))
    entries = {}
    for line in lines[1:]:
        if not line.strip():
            raise ValueError('Blank native mapping row: ' + str(path))
        row = json.loads(line)
        if (not isinstance(row, list) or len(row) != 2 or not isinstance(row[0], str)
                or re.fullmatch('[0-9a-f]{16}', row[0]) is None):
            raise ValueError('Malformed native mapping row: ' + str(path))
        key, value = row
        if key in entries and entries[key] != value:
            raise ValueError('Conflicting duplicate native mapping input: ' + key)
        entries[key] = value
    return lines[0], entries


def export_mappings(producers, outputs, toolchain, observations, *, repository_root=None):
    """Export ordered producers already validated against reconstructed tasks.

    Workspace cwd is a conservative namespace boundary; no caller assertion can
    merge different workspace layouts. The first explicitly ordered producer is
    primary. Additional incompatible groups remain native JSONL beside it.
    """
    if not producers:
        raise ValueError('Publishing requires validated native mapping tasks')
    ordered = sorted(enumerate(producers), key=lambda pair: (pair[1][0].get('export_order', pair[0]), pair[0]))
    groups = {}
    for _, (task, result) in ordered:
        path = Path(task['mapping'])
        if (not valid_receipt(result.get('receipt'), cwd=task['cwd'])
                or result.get('mapping_sha256') != observations.hash_file(path)):
            raise ValueError('Mapping producer lost its successful receipt/output identity')
        header, entries = read_mapping(path)
        observations.hash_file(path)
        domain = {'workspace': str(Path(task['cwd']).resolve()),
                  'toolchain': toolchain, 'platform': [platform.system(), platform.machine()],
                  'format': json.loads(header), 'layout': 'native-lake'}
        key = digest(domain)
        group = groups.setdefault(key, {'domain': domain, 'header': header, 'entries': {},
                                        'producers': [], 'modules': [], 'labels': []})
        for input_hash, output in entries.items():
            if input_hash in group['entries'] and group['entries'][input_hash] != output:
                raise ValueError('Conflicting duplicate native mapping input: ' + input_hash)
            group['entries'][input_hash] = output
        group['producers'].append(task['id'])
        group['modules'].extend(task.get('modules', task.get('identity_modules', ())))
        group['labels'].append(task.get('export_label', task['id']))
    outputs = Path(outputs)
    outputs.parent.mkdir(parents=True, exist_ok=True)
    exported = []
    for index, group in enumerate(groups.values()):
        path = outputs if index == 0 else outputs.with_name(outputs.name + '.groups') / f'{index:04d}.jsonl'
        if repository_root is not None and path.resolve().is_relative_to(Path(repository_root).resolve()):
            raise ValueError('Mapping export escaped into its source repository')
        if any(path.resolve() == Path(task['mapping']).resolve() for task, _ in producers):
            raise ValueError('Mapping export would overwrite its producer evidence')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(group['header'] + '\n' + ''.join(
            json.dumps([key, value], separators=(',', ':')) + '\n'
            for key, value in sorted(group['entries'].items())))
        exported.append({'path': str(path), 'sha256': file_hash(path), 'primary': index == 0,
                         'domain': group['domain'], 'producers': group['producers'],
                         'labels': group['labels'], 'modules': sorted(set(group['modules']))})
    observations.assert_stable()
    return exported
