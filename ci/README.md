# Common Lean CI

`lean-incremental-ci` is the shared Python 3.11+ implementation for Aglib,
Quillen, Motivic and R5Lab. Consumers provide one `.github/lean-ci.toml`, data-only
policy files and a short pinned reusable-workflow caller. Mathematical dependency
pins and the CI tooling release remain independent.

## Layout

```text
ci/
  pyproject.toml
  README.md
  src/lean_ci/
    application.py       # lifecycle and installed implementation identity
    configured.py        # declarative composition
    cli.py               # public commands
    project/             # configuration, source/dependency graphs, scope, imports
    checks/              # native, source/style guards, replay, Lean assets
    execution/           # runner, observations, runtime, resources, build/progress
    transport/           # GitHub history, cache, requests, frozen execution
  tests/
    project/
    checks/
    execution/
    transport/
    fixtures/
```

`project` owns source meaning and affected selection. `checks` owns checker
predicates and fixed Lean programs. `execution` runs guarded tasks and retains
input-keyed successes. `transport` admits external evidence and moves qualified
artifacts. `Application` and `ConfiguredAdapter` compose these responsibilities;
there are no compatibility modules or consumer Python adapters.

## Install and use

Install the immutable tooling release selected by the reusable workflow:

```sh
python3 -m pip install /path/to/aglib/ci
```

From a source checkout, `PYTHONPATH=/path/to/aglib/ci/src` selects the same package.
All commands use `python3 -m lean_ci` (or the installed `lean-ci` entry point):

```sh
python3 -m lean_ci scope --root . --config .github/lean-ci.toml
python3 -m lean_ci prepare --root . --config .github/lean-ci.toml
python3 -m lean_ci check --root . --config .github/lean-ci.toml \
  --state /absolute/scratch/state --progress /absolute/scratch/progress
python3 -m lean_ci imports --root . --config .github/lean-ci.toml --check
python3 -m lean_ci imports --root . --config .github/lean-ci.toml --write
```

Use `--target MODULE` for explicit scope and `--requested-base REF` to widen the
accepted comparison. Hosted CI uses `plan`, `source`, `native`, `finalize` with
one admitted plan and external state. `request --bundle PATH` prepares an admitted
native request; `execute` consumes its exact synchronized source, and
`execute --verify-only` verifies retained receipts without scheduling native work. Run `python3 -m lean_ci COMMAND --help` for that command's arguments.

Normal proof iteration remains a focused Lake build in a prepared workspace.
Final checks retain source/style/budget guards, selected compilation, builtin and
canonical per-origin declaration lint, selected Test/client proofs, axiom and
private/generated inventory checks. Selection follows old/new reverse-import
edges. Tests run through Lake without duplicate whole-Test replay. Unknown inputs
and unavailable history fail visibly; they do not request blanket rebuilding.

Dependency updates follow the old and current pinned external import graphs,
including indirect imports and client consumers. When hosted planning needs
missing source evidence, it fetches exact Git commits before selecting the scope.
This acquires source only; native preparation and compilation follow afterward.
Source-rule and budget changes inspect affected source bytes without scheduling
mathematical builds or native style checks solely for that policy change.

Declaration lint uses a fixed isolated runtime-first environment for each origin.
Older umbrella or target-first successes are not relabelled as that predicate.
Initialization retains currently uncovered obligations across failed heads;
compatible individual successes and compilation artifacts survive repairs.
Finalization aggregates existing results and schedules no checker or compiler.
Only qualified coverage permits native-baseline and publication claims.

`imports` defaults to checking configured products. Explicit writes validate the
complete proposed graph, ownership and source/policy/HEAD correspondence before
atomic file replacements. Curated and manual facades retain their owners.

## Library configuration

[Aglib's configuration](../.github/lean-ci.toml) includes an independent client;
the smallest package starts with:

```toml
schema = 1
package_dir = "."

[roles]
production = ["Library"]
tests = ["LibraryTest"]
```

Roles name actual Lake libraries or executables. `sources` owns extra Lean paths
as support, examples, diagnostics or archived references. Every maintained source
has exactly one owner; references supply no native proof coverage. Nested packages
use `package_dir` and clients keep independent package coordinates.

Top-level `formal_only`, `expected_failure` and `controls` contain exact paths.
Expected failures can be auxiliary files; compile-pass controls require a Lake
module identity. Their role changes are explicit in the selected scope.

`policy` names typed data files. Source-layout rules use `style`, finite budgets
use `budget`, justified source exemptions use `exceptions`, and Batteries
suppression pairs use `nolints`. The common native predicates remain fixed;
configuration supplies no commands or Python callbacks. Policy-reference order
matters when later files override earlier rules. See explicit replay below for
the separate artifact `inventory` policy.

## Explicit mathematical adoption

Replay remains outside ordinary CI and requires an explicit selection:

```sh
python3 -m lean_ci replay --root . --config .github/lean-ci.toml \
  --receipt-dir /absolute/scratch/replay --modules SELECTED_MODULE
```

`policy.inventory` describes artifact selection and forbidden prefixes for this
explicit replay. Ordinary axiom/inventory checks instead record constants from
the selected defining origins; they introduce no whole-cache scan.

Use `--workspace CLIENT_ID` for an independent configured package. `--all` requests
an explicit broader positive/support diagnostic; omission never selects it.
Formal/control probes retain their role labels. The installed LeanChecker,
most-private module parts, bounded task joins, resource caps, drift checks and
original module receipts retain their existing semantics. Replay observations do
not establish mathematical interpretation, premise validity or whole-library
acceptance. Retained legacy driver markers and compatibility keys remain stable.

## Validation

From the Aglib checkout:

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=ci/src python3 -P -m unittest discover \
  -s ci/tests -t ci -p 'test_*.py'
```

The suite uses isolated source/Git fixtures and small Python children. Native
checks skip unless prepared prerequisites are explicitly supplied; a Python-only
pass does not claim native coverage. The bounded native-cache harness is
`tests.execution.native_fixture`, with data under `ci/tests/fixtures/quartz`.
It remains an explicit native operation under its lease, not an implicit test run.
