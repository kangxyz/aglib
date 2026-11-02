# Minimal Mathlib-style CI

The template is adapted from Mathlib `d13f23b7`'s
[build_template.yml](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/.github/workflows/build_template.yml).
Callers supply the Lake package directory and nonempty production `build-targets`.
An optional `check-targets` string, empty by default, names extra helper targets
that Test builds alongside its checker tools. It never changes Build's targets
or mathematical artifact. For example, a caller can build `R5Lab Essays` in
Build and supply `Checks` separately as a Test helper.
`LAKE_NO_CACHE=true` follows Mathlib by disabling automatic package build
downloads from Reservoir/GitHub. This is separate from
`LAKE_ARTIFACT_CACHE=true`, which keeps native project artifacts available.

The job descriptions below cover ordinary incremental mode;
[cache-only differences](#native-root-seeds-and-cache-only-runs) are specified below.

- `build` restores caches, configures the pinned toolchain, obtains the Mathlib
  cache, imports published root and resolved `kangxyz/*` Git dependency caches,
  and incrementally builds only the production targets. It saves completed
  compilation, stages the production build's native mappings and outputs, and
  uploads that mathematical artifact for Test. It also snapshots the native
  `artifacts/` and `outputs/` directories as a compressed, same-run dependency
  fallback, separate from the public root-only artifact. No package checkouts or
  working build directories enter that fallback. It does not prepare checker tools
  or an auditor, run generated-entry or text-style checks, or build `check-targets`.
  Its final report requires the production build to succeed; checker failures
  belong to Test and do not change Build's result. Production Build is not retried.
  The first step records a compiler deadline 330 minutes after the Build job
  starts, including checkout, cache restoration, setup and dependency downloads.
  Production Lake receives only the time remaining, through GNU `timeout` with
  `SIGINT` and a sixty-second kill grace period. An already expired deadline
  skips Lake; timeout exit 124 or forced-kill exit 137 fails Build, so Test and
  Publish cache do not run. The job limit is 360 minutes, reserving about thirty
  minutes for the existing cache save and partial-output staging. Cache saving
  still runs after compiler failure or cutoff, before staging. A later run on
  the same branch restores compatible saved outputs and continues incrementally;
  no automatic rerun is scheduled. Network failures or runner teardown can still
  prevent cache delivery.
- `test_lint` requires successful Build. Its separate runner also imports the
  published root/dependency seeds. It downloads this run's mandatory
  `cache-staging` artifact, overlays its native mappings/artifacts with
  `lake cache unstage --force-overwrite`, and verifies only the production targets
  with `LAKE_RESTORE_ARTIFACTS=true lake build --no-build --rehash`. A missing
  artifact or incomplete native output fails the job before checker preparation.
  This follows Mathlib's
  [same-run staging transfer and completeness check](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/.github/workflows/build_template.yml#L444-L479).
  An optional Actions cache miss or restoration failure first downloads and
  restores Build's mandatory same-run dependency snapshot, including dependency
  outputs Build compiled that have no public release. It also obtains pinned
  Mathlib artifacts through Build's existing cache command. Recovery runs before
  the mandatory current-run root overlay. Successful output verification,
  rather than a warm-cache outcome, enables
  the later checks.
  Test then incrementally builds the Batteries declaration-linter, Mathlib
  text-style and `mk_all` executables plus any `check-targets`, using its restored
  caches. Mathlib's `mk_all --lib <root> --check` verifies the generated production
  entries without rewriting them; `lake --no-build exe mathlib/lint-style
  <production-roots>` scans the full import lists without automatic fixes.
  Both source checks collect feedback when checker preparation succeeds.
  Test also runs `lake test` and declaration lint. A caller containing
  `.github/lint/run.sh` uses that CI adapter; other callers retain
  `lake --no-build lint <production-roots> -- --trace`. The adapter retains
  builtin lint and the configured Batteries declaration predicate, with bounded
  worker scheduling for the complete declaration set on every invocation.
  Unsupported driver configurations use the original full command.
  In-package tests compile incrementally. A failed Test or source check does not suppress
  the other available checker feedback. Failed checker preparation skips checks
  needing those tools and fails the final Test report.
  Declaration lint has a twenty-minute GNU `timeout`, a thirty-second kill grace
  period and `LEAN_ABORT_ON_PANIC=1`. It retries once only for timeout exit 124;
  ordinary diagnostics, other errors and a second timeout remain failures.
  The step's forty-five-minute limit bounds both attempts, including adapter
  preparation and cache validation.
  The existing axiom step prepares the
  [pinned auditor used by lean-action](https://github.com/leanprover-community/axiom-audit/tree/46024e005996495c65ef609368e11ab39c4222e3)
  under `$LAKE_CACHE_DIR/axiom-audit`, checks its exact source revision and uses
  the package's unchanged toolchain. A cold cache clones/builds it there; a warm
  cache reuses the checkout and incremental outputs. Build never prepares the
  auditor, and its checkout is excluded from the dependency snapshot.
  The auditor reads built production roots and their imported
  closure; only `propext`, `Classical.choice` and `Quot.sound` are allowed.
  It does not compile the project or replay proofs. Deliberate negative Test
  fixtures are outside this production audit. Auditor preparation is independent
  of checker-tool preparation, so its feedback can survive another checker failure.
  The final Test report requires production-output verification, checker/helper
  preparation, generated entries, text style, in-package tests, lint and axioms
  all to succeed.
- `upload_cache` publishes only the staged mathematical compilation after Build
  and every required Test check pass, and only for trusted default-branch pushes.
  Failed or interrupted Build/Test work retains the always-run Actions cache saves
  where the runner can finish cleanup; this does not authorize release publication.
  First publication creates the release together with its asset and
  `--prerelease --latest=false`; later runs append an immutable run/platform asset
  to the existing release, preserving an already uploaded asset.

Native setup follows Mathlib's pinned
[setup-build-env action](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/.github/actions/setup-build-env/action.yml#L85-L103):
the official `https://elan.lean-lang.org/elan-init.sh` installer and `elan which
lake` select the package's unchanged `lean-toolchain`. Installer download retries
and at most three native toolchain-acquisition attempts handle transient failures.
Exhausted retries or failed Lean/Lake version checks fail setup. Both jobs run
setup from the caller's Lake package directory.

Necessary host adaptations are explicit: GitHub-hosted runners replace Mathlib's
self-hosted pool; GitHub caches/releases replace its Azure backend; native
`lake cache stage` replaces its project-specific cache staging executable.
Library and Test drivers live in Lake configuration. Generate each production
entry with `lake exe mathlib/mk_all --lib <root>`. Both native lint commands
receive the full production roots from `BUILD_TARGETS`, before `--` for `lake lint`.
This keeps builtin lint and Mathlib's text driver working when disjoint source
libraries have `roots = []`, leaving no default roots to infer. Every entry that
consumes production targets rejects an empty list. An empty `check-targets` list
is valid. Mathlib's text driver scans each selected root's complete import list
without changed-file filtering or automatic fixes. Test libraries use `TestName.+`
globs and `lake test`; they are not default production targets and have no
required generated `TestName.lean`. All callers use the same native mechanisms.

Each job restores `.lake` and the native cache directory together once. Build
and Test run on separate runners and each saves its completed compilation,
including partial progress on failure. Test's Actions restore warms dependency
and checker/auditor outputs; it does not substitute for the current Build artifact.
Before either job first invokes Lake, it removes only read-only, runner-owned
regular `*.ltar.hash` sidecars under the root package's `.lake/build/ir`.
Lake 4.34.1 writes these derived hash files directly. Runs 40818968404,
40846135998 and 40880003859 repeatedly failed while writing the inherited
`ToUnit.ltar.hash`; their logs establish failed writes and cache reuse, but
do not record the original sidecar's mode, owner or origin.
The cleanup requires runner-owned writable real build directories, skips
symlinks, and unlinks metadata without changing immutable artifact permissions
or shared cache inodes. The existing rehashed build regenerates those hashes;
writable sidecars, compiled outputs and cache mappings are preserved.
The same guarded cleanup runs again after cache preparation, immediately before
Build and Test's production-output verification. Startup cleanup alone does not
cover metadata introduced by later cache acquisition. In pinned Lake 4.34.1,
`Module.recBuildLean` can reuse compiled outputs, then `trackOutputsIfEnabled`
packs a missing `.ltar` for `-o` and `Cache.saveArtifact` rewrites its `.hash`
without first removing an existing sidecar. The job can therefore say
`Replaying` while performing a new failing archive/hash write; that heading does
not prove that the error was stored in an old log. A tiny isolated native Lake
regression reproduces this exact sequence and verifies repair without changing
the compiled output or native mappings. The AssociatedBundle report from run
41013572331 establishes the failing path and replay/packing sequence; its live
file mode, owner and original restoration point are unavailable. No saved error
logs are stripped and no failed native invocation is treated as successful.
The required current-run artifact overwrites production cache mappings. The
no-build check tests availability and applicability of those production outputs
against native inputs, without requiring checker outputs from Build. It does not
certify cryptographic provenance or integrity of cache bytes. As in Mathlib, this
transport relies on trusted cache producers. Downloaded transport archives are
removed after restoration so subsequent cache saves do not duplicate them. The dependency
snapshot transfers the existing native content store without a custom map
format; zstd compression is streamed to avoid an uncompressed tar copy. It is
not downloaded when Test's Actions restore succeeds with a matching key.
Both jobs use the same release-import loop for their root package and accepted
`kangxyz/*` Git dependencies from the resolved manifest, including inherited
dependencies. Native `-o` exports only the producer's root package, so each
upstream needs its own mappings. The existing native release transport serves
both CI and explicit local downloads. For the root, the requested producer
defaults to the current consumer SHA; dependencies retain their configured pins.
Fetch the exact `lean-native-<producer>` release first; otherwise try at most five
matching assets from 20 recent releases. New asset names include OS, architecture and toolchain;
`producer.json` binds repository, actual producer SHA, package and full compiler.
The release tag must target that producer SHA. Root downloads register mappings
with `lake --no-build cache unstage <staging-directory> --force-overwrite`, without
a dependency selector. Dependencies retain
`lake cache unstage <staging-directory> <manifest-package-name>`, including quoted
hyphenated selectors. Logs report actual producer and consumer/pin separately.
Existing `lake-native-cache-<run>-<attempt>.tar` assets remain optional legacy
seeds; current Lake input hashes decide their applicability. Downloads use the
normal repository token's public-read access, without a cross-repository secret.
Unavailable or incompatible seeds leave the ordinary incremental build in place.
Archives are unpacked only as flat regular native files, and temporary downloads
are removed before saving the Actions cache. This is cache acquisition, not an
additional mathematical check. Configured check predicates and release-publication
conditions are unchanged.

## Native root seeds and cache-only runs

The manual `ci.yml` entry accepts `native-root-producer`, `native-root-asset`,
`native-root-sha256` and `native-cache-only`. Defaults preserve normal incremental
builds and normal cache saves. An explicit root asset selects that exact producer
release asset; its optional SHA-256 is checked before extraction. The existing
flat native tar format and `producer.json` metadata are retained. Producer SHA
identifies the actual staging checkout, not a relabelled consumer or prior native
invocation; Lake's current source/import/options/compiler inputs decide reuse.

For an Aglib main-branch run with `native-cache-only=true`, producer, asset and
SHA-256 are required. Both jobs require a warm Actions-cache match and import the
same root/test asset. The metadata must match the full compiler; `toolchain` and
`manifest_sha256` bind the selected pins. Measured `root_build_bytes` and
`root_build_entries` admit conventional output restoration in addition to the
flat native files. Download/import and later staging gates
check live disk, inode and RAM availability. A missing or incompatible seed fails
without the ordinary Mathlib-download or compiler fallback.

Strict Build verifies production, AglibTest and required checker-tool availability
with native `--no-build --rehash`, then exports production outputs without
compilation. Strict Test materializes imported AglibTest outputs before applying
the mandatory current-run Build production overlay. It retains production-output
verification and every configured generated-entry, style, Test, declaration-lint
and production-axiom predicate, with the same production roots and accepted axioms.
Checker, test and auditor preparation also forbid compilation in this mode. This
changes artifact availability/failure behavior, not mathematical check coverage.

Strict mode suppresses Build's duplicate full Actions-cache save. After every
required Test outcome and quiescence succeed, it can save one complete `.lake`
and native-cache generation. The local Node24 action uses the public pinned
`@actions/cache` 6.1.0 `saveCache` API under
`prlimit --fsize=10000000000:10000000000`; its tar/zstd descendants inherit the
hard 10,000,000,000-byte file limit. On Linux the official SDK creates one compressed
archive, without a separate disk tar. Admission reserves the cap plus runner
margin and SDK installation allowance. Overflow, a nonpositive cache ID or an
absent matching main cache entry is failure. The saved ID, key, version and actual
size are checked through the normal read-only cache API. Other cache generations
remain subject to the repository's configured quota and ordinary eviction policy.

No mode fabricates GitHub check success from native receipts. A published seed,
successful native readiness, completed configured checks and persistent cache
delivery are distinct observations. Source changes, service failures or insufficient
resources can still prevent delivery. Ordinary runs retain their previous save
behavior; release publication still requires the existing successful-check and
default-branch-push conditions.

Run steps use a native systemd scope, dropping back to the runner UID/GID and
preserving its working directory, environment and selected toolchain. The
historical aggregate allowance is 13824 MiB, reduced only when physical RAM
minus a 2048 MiB runner/system reserve is smaller. Swap is disabled for that
scope, and the Actions runner stays outside its combined memory limit. The
scope gets a unique explicit name recorded under this run, attempt and job in
`RUNNER_TEMP`. Before either cache save, an always-run step outside those scopes
synchronously stops only the recorded units. Systemd scopes remain live while
any member process remains, so this also settles Lake/Lean descendants left when
Actions cancels the outer command. Cache saving and partial-output staging are
blocked if scope quiescence fails; normal compiler failure still saves completed
outputs after quiescence. No unrelated job or global process list is targeted.
This addresses the observed run 41004511190 cancellation race: cache tar reported
`outputs/Aglib: file changed as we read it` before post-job orphan cleanup killed
the old timeout, Lake and Lean. Systemd owns the scope stop semantics; the
regression exercises recorded-scope selection and a live synthetic cache writer.
See [scope lifecycle](https://www.freedesktop.org/software/systemd/man/latest/systemd.scope.html)
and [synchronous stop](https://www.freedesktop.org/software/systemd/man/latest/systemctl.html).
The maintained libraries all use weak `-M12800 -j4` frontend arguments: a
12800 MiB managed-allocation limit and four threads for their own modules.
Existing pinned dependencies and the separate auditor retain their own compiler
arguments; the aggregate scope also bounds those processes. These resource-only
arguments do not change native build traces.
Lake's runtime pool retains the historical `LEAN_NUM_THREADS=1`; the available
CPU count is logged separately. This is not a promise of a particular number
of simultaneous compiler processes. Ordinary failure can still execute the
existing cache saves; VM/runner teardown remains outside that guarantee. The retired manual cache-client workflow is no longer present.

The focused regression suite uses Python, PyYAML, tar and zstd:
`PYTHONPATH=scripts python3 -m unittest discover -s scripts/tests -p test_lean_ci_workflow.py -v`.
Callers use the display name `GitHub CI` and retain each repository's existing
concurrency-group identity.
`cancel-in-progress: false` with `queue: max` serializes runs without cancelling
the running job or replacing an already pending run.
Nightly automation, PR labelling, bibliography checks, style-fix bots,
downstream-client jobs and the old Python orchestration are outside this template.
Independent mathematical review retains its governing requirements. This workflow
adds no kernel replay, separate client checks or extra acceptance stages.

Local `scripts/check.sh` calls the unified toolkit documented in
[development](../docs/DEVELOPMENT.md#local-verification-and-ci). The three
libraries' tools live in that one package. Its check set and independent axiom
feedback use these same native mechanisms with existing local source guards.
Shared-artifact ctime changes trigger content rechecking rather than a new
validation attempt. The old Python
CI/baseline/frozen-request protocols and duplicate custom auditor are retired;
this does not modify the public YAML or broaden mathematical acceptance.

## Declaration-lint execution

The CI-only adapter in `.github/lint/` uses the package's existing toolchain and
Batteries APIs. It backports the full-scope worker scheduler from
[Batteries PR #2026](https://github.com/leanprover-community/batteries/pull/2026).
The pinned old implementation creates a task for each declaration/linter pair;
the adapter assigns batches of 64 declarations to a bounded worker pool and
retains only reported failures. Every enabled linter, including slow linters,
still checks the complete original declaration set in the full imported root
environment. It does not filter changed modules or reuse lint results.

Builtin lint remains a required check. The driver, root selection, suppression
files and production options retain their native meaning. Native
`lake --no-build --builtin-only lint <production-roots>` runs first, and the
declaration driver still runs if builtin lint reports findings. Their exit
statuses are combined as in the original command. The batched backend gives each
declaration/check fresh Core and Meta state, a distinct name generator and its
own configured heartbeat budget. Interrupts propagate as failures. Per-batch
progress reports include checked declaration counts and elapsed time. Unknown
linter implementations retain the pinned original full scheduler.

The adapter is compiled as a small native executable package under
`.lake/lint-runner`, requiring the already prepared Batteries package by path.
It does not check out or build another copy of Aglib or Mathlib. Ordinary Lake
compilation and the existing Actions cache reuse the executable; declaration
checks themselves always run. The private tool build explicitly selects its
generated TOML and refreshes only that tool's dependency resolution while keeping
the package toolchain. Restored tool configuration or path entries cannot select
a different executable or provider. The workflow passes `CI_LINT_NO_BUILD=true`
for strict native cache-only runs; private-tool preparation then adds native
`--no-build` while retaining the generated config, dependency update and toolchain
selection. Missing tool/provider outputs fail instead of compiling. The default
preparation and unsupported full-command fallback retain their existing behavior.
As in
[Batteries PR #2028](https://github.com/leanprover-community/batteries/pull/2028),
the imported environment is marked persistent only when there is exactly one
resolved declaration-driver root; multiple roots keep ordinary release behavior.

The adapter defaults to two workers, capped by the process's available CPUs.
`CI_LINT_WORKERS` selects another positive count, with the same CPU cap. The
worker setting applies only after preflight accepts the adapter. Build, Test
and unsupported native fallbacks retain their existing resource settings and
job scopes. Unsupported toolchains, provider
versions or driver configurations execute the original configured
`lake --no-build lint <production-roots> -- --trace` command. Preflight makes that
decision before the adapter imports the dependency API, including root package
overrides and competing root/provider configurations. Production Lake
configuration and dependency pins remain unchanged.

The existing twenty-minute attempt limit, retry policy, final Test report and
Publish cache gate still require the complete current checks to succeed.
