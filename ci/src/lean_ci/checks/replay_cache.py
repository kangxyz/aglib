#!/usr/bin/env python3
"""Hash root/client configuration, excluding package versions and cache storage policy.

The historical schema tag is retained so relocation does not invalidate replay keys.
Requires Python 3.11+. Executable Lake configurations are always hashed raw.
"""
import hashlib
import json
import math
from pathlib import Path
import tomllib


SCHEMA = 'aglib-project-cache-config-v1/typed-json-v1'
PACKAGES = ('',)


def _canonical(value):
    """Preserve TOML scalar types and array order; sort table keys."""
    if isinstance(value, dict):
        return ['table', [[key, _canonical(value[key])] for key in sorted(value)]]
    if isinstance(value, list):
        return ['array', [_canonical(item) for item in value]]
    if isinstance(value, bool):
        return ['bool', value]
    if isinstance(value, int):
        return ['int', str(value)]
    if isinstance(value, float) and math.isfinite(value):
        return ['float', value.hex()]
    if isinstance(value, str):
        return ['string', value]
    raise ValueError(f'unsupported TOML scalar: {type(value).__name__} ({value!r})')


def config_hash(root: Path, packages=PACKAGES) -> str:
    """Return the semantic configuration digest or raise on unusable inputs."""
    entries = []
    for package in packages:
        for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
            relative = package + name
            data = (root / relative).read_bytes()
            if not data.strip():
                raise ValueError(f'{relative}: required input is empty')
            if name == 'lakefile.toml':
                try:
                    config = tomllib.loads(data.decode('utf-8'))
                    # Native cache storage/restoration does not change compiler
                    # inputs. Retain the existing schema so enabling it can
                    # recover conventional outputs from pre-migration keys.
                    for field in ('version', 'enableArtifactCache', 'restoreAllArtifacts'):
                        config.pop(field, None)
                    content = _canonical(config)
                except (ValueError, UnicodeError) as error:
                    raise ValueError(f'{relative}: {error}') from error
            else:
                content = ['raw', data.hex()]
            entries.append([relative, 'present', content])
        relative = package + 'lakefile.lean'
        path = root / relative
        entries.append([relative, 'present', ['raw', path.read_bytes().hex()]]
                       if path.exists() else [relative, 'absent'])
    serialized = json.dumps([SCHEMA, entries], ensure_ascii=True,
                            separators=(',', ':'), allow_nan=False)
    return hashlib.sha256(serialized.encode('utf-8')).hexdigest()
