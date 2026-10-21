"""Invoke the reviewed fixed Lean auditor with structured module-name data."""
import hashlib
import json
from pathlib import Path
import re

from library_sources import IDENT, MODULE


AUDIT_DRIVER = 'ci/lean/SelectedAudit.lean'
AUDIT_DRIVER_SHA256 = 'bec83bb4b5884b07b674ba7ee945403dcc3f8ed0187b8a3fda46da6b7590389b'


def selection_data(modules):
    if not isinstance(modules, (list, tuple)) or not modules:
        raise ValueError('Audit module selection must be a nonempty list')
    result = []
    for name in modules:
        if not isinstance(name, str) or MODULE.fullmatch(name) is None:
            raise ValueError('Invalid audit module name: ' + repr(name))
        components = [part[1:-1] if part.startswith('«') else part
                      for part in re.findall(IDENT, name)]
        if any(not part or part in {'.', '..'} or any(
                char in '/\\' or ord(char) < 32 or 127 <= ord(char) <= 159 for char in part)
               for part in components):
            raise ValueError('Invalid audit module-name component: ' + repr(name))
        result.append(components)
    return json.dumps(result, ensure_ascii=False, separators=(',', ':'))


def validate_driver(root):
    source = (Path(root) / AUDIT_DRIVER).read_bytes()
    if hashlib.sha256(source).hexdigest() != AUDIT_DRIVER_SHA256:
        raise ValueError('Native semantic policy changed: unreviewed fixed audit driver')


def audit_command(root, modules):
    validate_driver(root)
    return ['lake', 'env', 'lean', '-j1', '--run', AUDIT_DRIVER, selection_data(modules)]
