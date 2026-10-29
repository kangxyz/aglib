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

- `build` restores caches, configures the pinned toolchain, obtains the Mathlib
  cache, imports published native caches for resolved `kangxyz/*` Git dependencies,
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
- `test_lint` requires successful Build. It downloads this run's mandatory
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
  Test also runs `lake test` and `lake --no-build lint <production-roots> -- --trace`.
  In-package tests compile incrementally. Batteries declaration lint retains its
  ordinary package-wide predicate. A failed Test or source check does not suppress
  the other available checker feedback. Failed checker preparation skips checks
  needing those tools and fails the final Test report.
  Declaration lint has a ten-minute GNU `timeout`, a thirty-second kill grace
  period and `LEAN_ABORT_ON_PANIC=1`. It retries once only for timeout exit 124;
  ordinary diagnostics, other errors and a second timeout remain failures.
  The step's twenty-five-minute limit bounds both attempts.
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
The required current-run artifact overwrites production cache mappings. The
no-build check tests availability and applicability of those production outputs
against native inputs, without requiring checker outputs from Build. It does not
certify cryptographic provenance or integrity of cache bytes. As in Mathlib, this
transport relies on trusted cache producers. Downloaded transport archives are
removed after restoration so subsequent cache saves do not duplicate them. The dependency
snapshot transfers the existing native content store without a custom map
format; zstd compression is streamed to avoid an uncompressed tar copy. It is
not downloaded when Test's Actions restore succeeds with a matching key.
Build discovers accepted `kangxyz/*` Git dependencies from the resolved manifest,
including inherited dependencies: native `-o` exports only the producer's root
package, so each upstream needs its own mappings. The existing native release
transport now serves both CI and explicit local downloads. Fetch the exact
`lean-native-<pin>` release first; otherwise try at most five matching assets from
20 recent releases. New asset names include OS, architecture and toolchain;
`producer.json` binds repository, actual producer SHA, package and full compiler.
The release tag must target that producer SHA. Downloads register mappings with
`lake cache unstage <staging-directory> <manifest-package-name>`, retaining quoted
hyphenated selectors. Logs report producer SHA and consumer pin separately.
Existing `lake-native-cache-<run>-<attempt>.tar` assets remain optional legacy
seeds; current Lake input hashes decide their applicability. Downloads use the
normal repository token's public-read access, without a cross-repository secret.
Unavailable or incompatible seeds leave the ordinary incremental build in place.
Archives are unpacked only as flat regular native files, and temporary downloads
are removed before saving the Actions cache. This is cache acquisition, not an
additional mathematical check. Build/Test/publication conditions are unchanged.

Run steps use a native systemd scope, dropping back to the runner UID/GID and
preserving its working directory, environment and selected toolchain. The
historical aggregate allowance is 13824 MiB, reduced only when physical RAM
minus a 2048 MiB runner/system reserve is smaller. Swap is disabled for that
scope, and the Actions runner stays outside its combined memory limit. The
maintained libraries all use weak `-M12800 -j4` frontend arguments: a
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

Local `scripts/check.sh` now calls the native CLI documented in
[development](../docs/DEVELOPMENT.md#local-verification-and-ci). It uses these
same native mechanisms with existing local source guards. The old Python
CI/baseline/frozen-request protocols and duplicate custom auditor are retired;
this does not modify the public YAML or broaden mathematical acceptance.
