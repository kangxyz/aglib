# Lean incremental CI

`lean-incremental-ci` is a Python 3.11+ package for incremental Lean CI execution
and evidence. Its runtime uses only the Python standard library. A repository
adapter supplies its targets, scope rules, audit/check commands, reviewed
baseline protocol and publication policy. The package does not infer a library's
mathematical coverage from the name of its roots or a successful workflow alone.

## Installation

Install from this directory with `python3 -m pip install ./ci`. The installed
console entry point is `lean-ci`; execution policy comes from a repository
adapter. Building the distribution uses setuptools. There are no runtime package
dependencies to download.

A source checkout can instead use `PYTHONPATH=ci` or a thin launcher that adds
its committed sibling `ci/` directory to `sys.path`. CI does not need to install
the package from the network. Repository compatibility launchers can re-export
the package API while keeping project-specific rules outside the package.

## Shared APIs

`lean_ci.source` owns Lean-name/path conversion, nested comment/string masking,
the import-header parser and import-surface recognition. The parser implements
the supported pinned Lean grammar: each import directive consumes one module;
body commands and quotations do not extend the header.

`lean_ci.state` exports `TemporalInputs`, `ReflectionGraph`, `Progress`, native
module identities, JSON helpers and receipt validation. One phase observer can
hash compiler binaries, libraries, raw optional policy inputs and native module
artifacts. Pass it as `ReflectionGraph(..., observations=observer)` to share
hashes and temporal guards. Content compatibility keys exclude temporal stamps;
mutation during a check, including changed-and-restored inputs, cannot create a
success record. Missing optional names and earlier import-resolution candidates
retain absence observations. A matching compilation trace alone does not prove
that a lint or audit succeeded.

`lean_ci.github` exports `GitHubAPI`, `EvidenceProtocol` and
`select(root, repository, default_branch, head, ..., protocol=protocol)`.
The caller explicitly configures:

- Workflow path, job name, native step and finalization step.
- Exact reviewed workflow SHA256 identities, classified as `legacy` or `core`.
- Exact legacy recipe path/hash identities.
- An optional frozen `legacy_heads` allowlist of exact source commit SHAs.
- Ordered core entrypoint paths and reviewed recipe hash tuples.

Unknown or absent recipes fail closed. A native job must succeed in the exact
successful run attempt; core protocols also require successful finalization.
Manual bases may widen the verified comparison range. The API never substitutes
the previous push for missing verification history. Authentication uses
`GH_TOKEN` or `GITHUB_TOKEN`; `GITHUB_API_URL` can select an API host. TLS
verification remains enabled, and transient retries are bounded.

An adapter can restrict legacy admission to a completely reviewed source commit
with `legacy_heads=frozenset({reviewed_commit_sha})`; other legacy candidates are
skipped while older history is searched. An empty set disables legacy admission.
`None` retains recipe-only admission and therefore explicitly relies on separate
review/trust of changed supporting sources. Mutable branch or tag names cannot
serve as allowlist entries. Exact workflow and recipe identities remain required
in either mode.

## Supported evidence boundary

The current native reader supports trace schema `2025-09-10` and `.ilean` JSON
version 5 from the pinned Lean 4.34.1 implementation. It follows all explicit
import metadata flags and resolves implicit compiler imports using actual search
paths and installation provenance. Standard Lake compilation is required;
custom `ModuleSetup.imports` overrides are outside this guarantee. Unsupported
metadata cannot authorize reuse. Other Lean versions require an intentional
compatibility review rather than an assumed format guarantee.

Lake owns compilation dependency identity. Normal CI uses shared `--rehash`
graph validation; saved check records do not waive it. Cache and recipe evidence
retain a reviewed, trusted-producer boundary. Exact entrypoint/workflow identities
do not authenticate arbitrary changed supporting code or establish mathematical
adoption. A repository must retain review of its adapter and supporting sources.

## Applications and repository adapters

`lean_ci.engine.Application(root, adapter, runtime=None)` exposes `plan`,
`run_phase` and `finalize`. `NativeRuntime(root, resource_config=..., environment=...)`
provides guarded native execution. `ResourceConfig` uses `LEAN_CI_*` names by
default; optional variable aliases and parent-managed profiles are explicit
per-instance configuration, rather than global package state.
All native task working directories must resolve the same compiler and physical
runtime as the application root. The package checks those actual identities
before execution or check reuse and before saving a performed success; mixed
root/client installations are unsupported and rejected before acceptance.
Toolchain installation and Elan's selection configuration must remain immutable
during an attempt. A launcher performs its own read-only Elan lookup; observing
compiler files does not monitor arbitrary changes to external Elan overrides.

The adapter supplies these required methods:

| Method | Result or obligation |
| --- | --- |
| `plan(root, repository, default_branch, head, requested_base=None, api=None)` | Repository-owned baseline/scope/policy payload; no core envelope fields |
| `required_phases(root, payload)` | `['source']` or `['source', 'native']` |
| `validate_plan(root, plan)` | Reconstruct and validate repository scope and inherited policy |
| `tasks(root, plan, phase, directory)` | Nonempty ordered task dictionaries with unique IDs, commands and absolute working directories |
| `binding(root, task, toolchain, reflection=None, observations=None)` | Actual declared check inputs, logical arguments and compatible reflective closure |

Optional `custom_task`/`verify_custom_task` hooks implement repository-specific
checks. A task with `establishes_inputs=True` invokes optional `observe_inputs`
after deterministic setup. Optional `summary` adds coverage qualifiers, but
cannot overwrite core completion fields. Native records require successful
actual receipts; an adapter decides what its mathematical checks mean.

The package binds its actual executing implementation, including installed
`site-packages` sources. The canonical content fingerprint is independent of its
installation location and is included in plans, summaries and individual-check
keys. The source must stay stable throughout the attempt. Reusing receipts from
an identical relocated checkout retains their original execution paths as
provenance; a different logical working directory or repository changes the key.

A committed `ci_adapter.py` exports `create_application(root) -> Application`.
Then use either the installed console command or the source package:

```sh
PYTHONPATH=ci python3 -m lean_ci plan --adapter ci_adapter.py \
  --repository OWNER/REPO --default-branch DEFAULT_BRANCH \
  --head EXACT_COMMIT_SHA --state /absolute/runner-state
PYTHONPATH=ci python3 -m lean_ci source --adapter ci_adapter.py --state /absolute/runner-state
PYTHONPATH=ci python3 -m lean_ci native --adapter ci_adapter.py --state /absolute/runner-state \
  --progress /absolute/check-progress
PYTHONPATH=ci python3 -m lean_ci finalize --adapter ci_adapter.py --state /absolute/runner-state \
  --outputs /absolute/native-outputs.jsonl
```

Checkout/toolchain installation, upstream cache acquisition and publication
credentials remain the host workflow's responsibilities. Lake commands and APIs
own build dependency decisions; Python does not reconstruct their input hash.
The [Aglib adapter](../scripts/ci_pipeline.py) is a maintained integration. The
separate Quartz fixture is an explicit complete local test, not a substitute for
verified GitHub baseline selection in an incremental production repository.

## Bounded native integration

Run `python3 ci/native_test.py --state /absolute/fresh-fixture` with the prepared
pinned toolchain. Optional `--lease /absolute/native.lock` acquires a nonblocking
POSIX compiler lease; it never queues. `--resource-prefix` and repeatable
`--profile-key` select the caller's resource names without library-specific names
in the harness.

The two-module fixture uses independent producer/consumer directories and
isolated local native caches. It intentionally fails after a completed proof
check, retains compatible artifacts/check progress, restores them under
`--no-build`, rejects an upstream-source change with old-only cache, then
restores current-input artifacts and completes. Reports distinguish those
expected failures from acceptance. There is no dependency update, remote cache
service or assumed cross-compiler compatibility. `--no-cache` alone is not a
universal network-denial mechanism; the fixture has no remote mappings or
remote dependencies.
