# Library-specific mathematical inspection

Standard development commands live once in the installed common `lean_ci`
distribution, selected independently of mathematical dependency pins:

```sh
python3 -m lean_ci prepare --config .github/lean-ci.toml --root .
python3 -m lean_ci check --config .github/lean-ci.toml --root .
python3 -m lean_ci imports --config .github/lean-ci.toml --root . --check
python3 -m lean_ci imports --config .github/lean-ci.toml --root . --write
```

Formal mathematical adoption remains an explicit, scoped command:

```sh
python3 -m lean_ci replay --config .github/lean-ci.toml --root . \
  --receipt-dir /absolute/scratch/replay --modules SELECTED_MODULE
```

Use `--workspace downstream` for the independent `Consumer` package. Replay
requires exact `--modules`/`--only`; broader positive/support diagnostics require
explicit `--all`. It is never an ordinary CI step. The shared implementation
preserves the installed LeanChecker function, native driver bytes and markers,
exact most-private module parts, bounded task joins, memory caps, input drift
checks and module-bound original receipts. Scope/role labels remain explicit;
an adoption probe does not establish whole-library or mathematical acceptance.
See [the adoption policy](../docs/DEVELOPMENT.md#kernel-replay-at-mathematical-adoption).

This directory retains only mathematical migration inspection:

| File | Consumer |
| --- | --- |
| `migration_helpers.py` | Read-only historical namespace/source routing; requires explicit source root, exact revision and source hash. Retired writer interfaces fail before writes. The lexer comes from the common package. |
| `test_migration_helpers.py` | Four finite contracts for source identity, routing/provenance and retired writer rejection. |

The mathematical helper preserves existing namespace maps and provenance data.
Its text projections do not select admissible mathematics or author redesigned
sources. Shared maintenance, build, cache, lint, inventory and replay helpers and
their generic fixtures belong to the common package, not copied wrappers here.
