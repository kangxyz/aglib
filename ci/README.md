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
artifacts. The shared runner keeps source, policy and compiler/runtime guards for
the invocation, with a separate native-artifact observer for each consuming
check. Content compatibility keys exclude temporal stamps; mutation during a
check, including changed-and-restored inputs, cannot create a success record.
Cache restoration or hardlink bookkeeping between completed checks can change
native metadata without changing their compatible content. Fresh reconstructed
verification observes the current native closure through final publication.
Missing optional names and earlier import-resolution candidates
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

`execution_diagnostics` reports measured binding, command, record-write and
reconstruction costs, plus observed source/native scan counts and times. Operation
times are inclusive; parallel command times are sums, so they must not be added
to enclosing wall times. These fields are diagnostics, not coverage evidence.
Pure binding `inspection()` coalesces nested full scans at entry/exit; individual
file reads retain their own stamp checks. It must not enclose command execution.
Managed cache identity normalizes invocation coordinates only after recognizing
the canonical wrapper and its content-addressed worker/sidecar. Their producer
hashes, Python runtime and semantic configuration remain in the key; unknown
wrappers retain their complete identities. Physical compiler/library hashes,
options and other search paths still bind reuse. Actual wrapper, configuration
and resource identities remain guarded within each run.

The package binds its actual executing implementation, including installed
`site-packages` sources. The canonical content fingerprint is independent of its
installation location and remains in plans, summaries and check provenance.
Generic executor repairs do not invalidate compatible check results: their
commands, checker/policy sources, native imports, runtime and environment still
bind reuse. Implementation and input drift guards stay active throughout each
attempt. Reusing receipts from
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

The reviewed Lean fixture files live in [fixtures/quartz](fixtures/quartz).
The harness verifies their content identities and copies them into each isolated
checkout; it does not construct Lean programs from Python strings. The upstream
transition copies the separate fixed `upstream9.lean` file over the fixture's
`Quartz/Upstream.lean`. The ordinary Aglib adapter also uses a fixed
[Lean audit entrypoint](lean/SelectedAudit.lean) with JSON name arguments; see the
[audit contract](../docs/CI.md#fixed-lean-audit-and-fixture-sources).

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

## Shared recipe and working-tree final checks

`lean-ci check --root REPOSITORY --adapter scripts/ci_pipeline.py` runs a
meaningful local final check on the scoped working-tree bytes. `--state` is
optional (a safe temporary receipt directory is allocated); `--progress PATH`
retains compatible individual-check successes across repairs. `--requested-base`,
repeatable `--target`, and `--outputs` are passed to the same policy/executor.
The local result records `source_basis.kind = working-tree`; it does not create a
CI plan or authorize CI publication. The existing committed `plan`, `source`,
`native`, and `finalize` entry guards remain strict. Ordinary proof iteration
continues to use direct incremental native compilation.

A local adapter supplies `local_inputs(root, requested_base=None, targets=())`
and `select_scope(root, requested_base=None, targets=(), source_basis=...)`.
The first hook inventories the source-selection, enrollment, pins, configuration,
checker and policy inputs; all are observed before the selector and source checks.
It returns repository-relative paths, including relevant absent/shadow candidates.
A directory entry may be `{'path': 'client', 'exclude': ['.lake']}` to watch
relevant enrollment names while deterministic ignored setup changes excluded
entries. Directory inventories certify current names/types, not transient
create/remove of unknown names absent at both observations; explicitly enrolled
missing paths keep the existing strict temporal parent guard. Such missing-path
guards can reject setup in the same parent. Before a native local final check,
finish the library operating guide's fixed ignored `.lake` directory/link setup,
without changing tracked manifests or pins; the check's setup then remains
idempotent. Source-only scope creates no caches. Committed CI retains its
existing deterministic setup timing. Existing files retain shared content hashes and
before/after temporal guards. This trusted adapter policy must include the full
scope; reconstructed tasks and receipts alone cannot prove its completeness.

`Application(root, adapter, runtime=None, package_cwd=None)` keeps the Git root
separate from the Lake package cwd (for example `REPOSITORY/lean`). Every task cwd
must stay inside the repository. Root/client workspaces receive separate actual
Lake search paths and `ReflectionGraph` instances; all use the same compiler and
runtime identity within an invocation. `Application.check(...)` uses the shared
`TaskRunner`, as do committed phases; optional `validate_local` and
`local_summary(root, plan, record)` hooks preserve library policy and qualified
coverage without overriding core success fields.

`lean_ci.recipe.native_recipe` accepts `source_checks`, `prepare`, at most one
`provider_gate`, `root_workspace`, `clients`, and ordered `exports`, plus
`phase='source'|'native'|'check'`. These contain the existing task dictionaries.
A workspace declares `id`, `cwd`, semantic `modules`, `selection='module'` or
`'library'`, and accepted `checks`. `before` tasks and an explicit `build_task`
retain an existing mixed library/module/executable Lake graph when needed. Lake
schedules each graph; the recipe adds no module scheduler. Semantic names remain
bare in source/reflection queries; `build.native_targets` renders `+MODULE` only
at the native command boundary. The public `build.build` defaults to module
selection; legacy task dictionaries without `build_selection` retain their
explicit library command meaning.

Reusable style/control checks deliberately use `kind='check'` and a declared
`input_boundary` plus complete binding `raw_inputs`; plain processes never gain
reuse semantics. Native checks retain their reflective binding. Deduplication and
reuse include commands, cwd, declared environment (`environment_keys` for extra
checker inputs), generated bytes, check inputs, and the declared boundary.
Setup tasks remain operations. `established_paths` can name precise inputs to
observe after deterministic setup; `establishes_inputs` retains the existing
adapter-wide `observe_inputs` hook. Generated audit/lint tasks can declare
`generated_path` and `generated_argument_index`, binding an explicit `--run`
program before trailing module arguments. Normalize that argument to
`<generated-input>` in the binding; the actual receipt retains its real path.

Every mapping producer retains its successful receipt, selected task and output
hash, including cache-hit builds. Export merges compatible same-workspace groups,
preserves the native Lake `2026-03-17` JSONL header, and rejects conflicting input
hash mappings. Different workspace namespaces remain separate native files.
The first workspace in `exports` is primary; explicit mapping tasks may set
`export_order` and `export_label`. The requested outputs path is the primary
group; `summary.mapping_groups` identifies every group's cwd, compiler/platform
domain, producers and modules, with additional files under `OUTPUT.groups/`.
Export/finalization never recompiles a graph to obtain another mapping.

## Frozen native execution without Git

`lean-ci execute REQUEST.json` (also `python -m lean_ci.frozen REQUEST.json`)
executes an already selected **native-only** recipe in a synchronized workspace.
It does not run local selectors, local source checks, Git baseline selection, or
committed CI finalization. This entry is distinct from `lean-ci check`, which
requires a Git working tree.

The request is a regular file included in the existing synchronized `SOURCE.files`
manifest. Its schema is:

```json
{
  "schema": 1,
  "adapter": "ci_adapter.py",
  "policy_inputs": ["ci_adapter.py", "helper.py"],
  "implementation": {"__init__.py": "exact SHA256 for each actual lean_ci owner"},
  "payload": {"scope": "the adapter's already selected scope and policy fields"},
  "coordinates": {"root": ".", "package_cwd": ".", "source_mapping": {}}
}
```

Use the full actual `implementation_identity()` map, not a version string.
Optional `tooling_files` maps explicitly admitted absolute immutable helper files
to SHA256 values; optional `absent_inputs` lists known package-relative missing or
shadow candidates. All source policy/check helpers must be explicitly enrolled;
these declarations remain trusted adapter policy rather than a completeness proof.
The payload cannot override the core source/runtime envelope.

The entry requires `--source-manifest` and `--expected-source`, or the exact
`LEAN_CI_SOURCE_MANIFEST` and `LEAN_CI_EXPECTED_SOURCE` environment variables
exported by the owned remote phase worker. The expected final source digest is
outside the included request, avoiding a self-reference. Admission verifies the
manifest owner, canonical files-map digest, every synchronized file's actual
bytes, the request/policy/helper enrollment, explicit tooling, and package pins
before loading policy. Unsafe paths, source symlinks, incomplete snapshots,
unknown implementation bytes, unadmitted Python helper origins, and ignored old
policy bytecode fail closed. The shared `TemporalInputs`, native runner, actual
runtime observation, reconstructed task verification and mapping exporter then
remain in force throughout execution. A declared `R5_LEAN_REMOTE_PROFILE` must be
explicitly enrolled by the adapter/runtime; execution cannot silently fall back
to local resource policy.

The usual factory remains `create_application(root)`. A package transported from
a repository subdirectory can instead provide
`create_native_application(root, package_cwd, source_mapping)` and return the same
adapter/recipe with explicit physical coordinates. Coordinates are relative to
`SOURCE.workspace`; no parent/sibling discovery or virtual filesystem is added.
For R5Lab the transport is `repo/lean` flattened to the remote package, with
`root=package_cwd='.'` and the exact mapping
`{'repository_package': 'lean', 'transport_package': '.'}`. Its admitted
`ci_adapter.py`, pins and native helpers are package-relative. Parent `infra/`
source checks remain local and separately qualified; they are not presumed to
have transferred through an illegal `../` include.

The result uses `source_basis.kind='transport-snapshot'` and
`status='succeeded'`, records the source digest and performed/reused checks, and
explicitly leaves local source coverage separate. It does **not** authorize
hosted CI completion. Acceptance must join it to the outer worker's successful
receipt with the same `expected_source`, workspace and owned phase command. The
entry does not reacquire the worker's workspace lock. `--state`, `--progress`,
and `--outputs` retain their external evidence/output roles; state is optional.

If all required individual receipts exist but final sealing failed, use
`lean-ci execute REQUEST.json --state ORIGINAL_STATE --verify-only` under a new
owned phase. It admits the same source, request, implementation and semantic
compiler/runtime, reconstructs every required task, and verifies retained
receipts without executing tasks or rebuilding. Incomplete or changed coverage
fails. The original `native.json` and failed outer receipt remain unchanged;
`native-verification.json` records the fresh verification. Its result marks
`verification_only`, no newly performed checks/compilation, and retained reuse.
It still needs the matching new outer receipt and cannot finalize hosted CI.

## Independent read-only check batches

Adjacent native check tasks can explicitly declare a common
`check_batch={'id': 'providers/declarations', 'jobs': 8, 'read_only': True,
'single_process': True}`. The last field promises at most one active compiler
per task. Local adapters select one job; remote jobs must fit the validated
parent profile. The runtime retains that profile and its compiler admission.
Only capped checks qualify; builds, setup, generated programs and native-output
producers cannot join the group. Changing import environments or linter
predicates still requires the library's accepted scope decision.

The coordinator performs bindings, cache lookups, receipt verification and
Progress writes. Only native command execution overlaps. Each compatible
success survives a peer failure; a retry executes missing/changed items.
Failure stops new admission and settles active checks. Interruption requests
cancellation through each existing owned process-group monitor before returning.
Libraries declare individual checks rather than implementing another process,
result or retry loop. A source graph may be memoized only behind complete
source-byte and enrollment observations for its actual parser domain.

Historical GitHub CI witnesses can retain an explicitly reviewed older owner set
through `EvidenceProtocol.historical_core_recipes`, a tuple of
`CoreRecipeVersion(paths, recipes, heads)`. Every historical alternative requires
a nonempty frozen allowlist of exact source commit heads, matched against the
resolved candidate commit; `None` and empty allowlists are rejected. The current complete owner set is checked first; only
explicit historical path/hash sets follow. There is no automatic tuple-prefix,
layout or missing-helper fallback, and existing protocols default to no history.
