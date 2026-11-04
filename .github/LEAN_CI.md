# Lean CI

[Aglib's workflow](workflows/ci.yml) calls the [shared Lean workflow](workflows/lean-ci.yml)
with production target `Aglib`. Build compiles the production targets. Test verifies
this run's production outputs and runs the package checks. Publish cache publishes
the verified production archive after both jobs succeed on a default-branch push.
[Local verification](../docs/DEVELOPMENT.md#local-verification-and-ci) uses
`scripts/check.sh` to run the native checks against an existing checkout.

## Runner routing

| Trigger | Build and Test | Publish cache |
| --- | --- | --- |
| Push to Aglib `main` | EC2 | GitHub-hosted Ubuntu 24.04 after both jobs succeed |
| Manual dispatch on `main` with `runner-profile=ec2` (default) | EC2 | Skipped |
| PR, push to another branch, or any other manual dispatch | GitHub-hosted Ubuntu 24.04 | Skipped |

The EC2 autoscaler matches the exact label set `self-hosted, linux, x64,
aglib-ec2-pilot` and caps the pool at one on-demand instance. Aglib gives Build
and Test 57,344 MiB (56 GiB) per native scope, eight Lake runtime threads, and
eight declaration lint workers. Build has a 240-minute job limit and a
180-minute compiler cap. Test has a 90-minute job limit. Publish cache uses
the workflow's hosted resource settings.

The main CI and the [manual EC2 probe](workflows/ec2-pilot.yml) share the
`Aglib CI-<ref>` concurrency group. `cancel-in-progress: false` and
`queue: max` let runs for the same ref finish in order. Each run uses its
own workflow snapshot.

Runner-local handoff is selected on the EC2 route when
`AGLIB_EC2_SHARED_HOST=true` and the layered checkpoint preflight succeeds.
The persistent runner service must retain the checkout between jobs and
expose `aglib-ci-shared-host-v1` in the root-owned file
`/etc/aglib-ci-runner-mode`. Build renews `aglib-pilot-expiry.timer` before
compiling. The deployed 360-minute watchdog covers both jobs and bootstrap,
and the autoscaler reclaims the instance after 900 seconds of confirmed
idle time. Keep these settings in Terraform. The manual probe with
`verify-handoff=true` checks that two jobs see the same runner and workspace.
With the repository variable unset, the workflow uses the artifact transfer
path. Unsupported layered layouts also use that path. If same-host mode is
selected but the runner marker is absent, Build fails before compilation.

The normal workflow routes PRs to hosted runners. GitHub assigns self-hosted
jobs by requested labels and groups. If external contributions expand, the
repository can require approval for all outside-contributor workflows. Review
their workflow changes and verify the autoscaler's repository and event filters
when tightening admission.
[GitHub's self-hosted runner security guidance](https://docs.github.com/en/actions/reference/security/secure-use#hardening-for-self-hosted-runners)

### Reusable workflow inputs

| Input | Default | Effect |
| --- | --- | --- |
| `package-directory` | `.` | Directory containing the Lake package |
| `build-targets` | Required | Space-separated production roots used by Build, production verification, lint and the axiom audit |
| `check-targets` | Empty | Extra Lake targets built with the check tools in Test |
| `runner-labels` | `["ubuntu-24.04"]` | JSON array encoded as a string for Build and Test |
| `reuse-build-host` | `false` | Requests runner-local handoff for an eligible layered checkout |
| `native-memory-mib` | `13824` | Requested aggregate memory limit per native scope |
| `lake-threads` / `lint-workers` | `1` / `2` | Lake runtime threads and requested declaration lint workers |
| `build-lake-threads` | `0` | Inherits `lake-threads`. A positive override applies only to the production Build step |
| `job-timeout-minutes` | `360` | Test job limit and default Build job limit |
| `build-job-timeout-minutes` | `0` | Inherits the job limit. A positive value sets the Build job limit |
| `build-compiler-minutes` | `0` | Uses the remaining time before the checkpoint reserve. A positive value caps that remaining time |
| `first-ci-cache` | Empty | Reviewed exact cache seed for the separate branch promotion procedure |

## Execution order

### Build

1. Set the compilation deadline before checkout. Check out the run revision and
   determine the cache mode. Download optional working checkpoints and, where
   applicable, a broad cache. Cross-runner builds keep the Lake native cache
   under `$RUNNER_TEMP/lake-native-cache`. Same-host builds put it under
   `.lake/ci-host-handoff/native-cache` so it survives per-job temp cleanup.
2. Install Elan and resolve Lake from the committed `lean-toolchain`. The
   workflow retries the installer download and attempts toolchain acquisition
   up to three times. It verifies the Lean and Lake binaries before continuing.
   Build obtains Mathlib artifacts with `lake exe cache get` and tries published
   native seeds for eligible resolved `kangxyz/*` Git dependencies.
3. Validate the materialized dependency layout when using layered checkpoints.
   Apply optional checkpoints in tools, dependencies, root order. Build fetches
   the tools checkpoint only for runner-local handoff. Run
   `lake build --rehash <production-roots> -o "$RUNNER_TEMP/outputs.jsonl"`.
   Checker tools and `check-targets` belong to Test.
4. Stop the recorded native scopes before reading build outputs. Stage any
   available native output mapping. In layered mode, stop the staging scopes
   before packing the root and dependency checkpoints. These saves preserve
   completed work from successful and failed compilation attempts subject to
   the job and scope gates below. Ordinary legacy builds save the combined
   cache after the first scope stop, before staging.

`LAKE_NO_CACHE=true` disables Lake's automatic package build downloads.
`LAKE_ARTIFACT_CACHE=true` enables the native artifact store used by staging
and restoration. The explicit Mathlib download and published dependency
imports are separate acquisition steps.

### Runner-local Test

After successful compilation and staging, Build places the tar, its SHA-256,
the Lean binary directory, and the handoff identity in the workspace or job
outputs. Test compares the identity against its runner name, repository,
commit, run ID and attempt, and verifies checkout `HEAD`. It adds the recorded
Lean binary directory to its job path and uses Build's native store and
dependency working trees. A mismatch fails the claim before the checks.

Test verifies the tar digest, then runs [verify-root.sh](ci-cache/verify-root.sh).
The helper temporarily moves aside the expanded root `.lake/build` and
unstages the archive into an empty native store. It runs
`lake build --no-build --rehash` against the original checkout and dependency
trees and restores the original root build before running the checks. The
cold root exposes missing archive outputs that a warm root could mask.

### Cross-runner Test

1. Check out the same run revision, select the pinned Lean toolchain and
   restore optional caches. On the layered path, download the full
   `build-dependencies` archive from this run's Build even when optional caches
   hit. Fetch pinned dependency sources with `lake env true`, validate their
   layouts, apply optional root and tools checkpoints, then overlay the current
   dependency closure.
2. On the legacy path, try the combined Actions cache first. A miss or failed
   restore recovers the current Build's compressed native `artifacts/` and
   `outputs/` and runs Mathlib cache acquisition.
3. On either cross-runner path, download this run's `cache-staging` and apply
   `lake cache unstage --force-overwrite` after the other overlays. Verify the
   production roots with `LAKE_RESTORE_ARTIFACTS=true lake build --no-build --rehash`.
   A missing or inapplicable current artifact fails verification before
   checker preparation.

### Package checks and publication

Test prepares `batteries/runLinter`, `mathlib/lint-style`, `mathlib/mk_all`
and any `check-targets` with Lake. It then runs
`lake --no-build exe mathlib/mk_all --lib <root> --check` for each production
root, `lake --no-build exe mathlib/lint-style <production-roots>` over their
full import lists, `lake test`, and declaration lint. The entry and text
style checks leave sources untouched. Library and Test drivers come from
the package's Lake configuration.

The [pinned production auditor](https://github.com/leanprover-community/axiom-audit/tree/46024e005996495c65ef609368e11ab39c4222e3)
builds under `$LAKE_CACHE_DIR/axiom-audit` with the package toolchain. Test
checks its exact source revision before running the binary on each production
root with `lake env`. If the tools checkpoint restored build outputs without
a checkout, Test clones the pinned source into a temporary directory and
overlays it while keeping those outputs. The audit covers production roots
and their imported closure and allows only `propext`, `Classical.choice`
and `Quot.sound`.

Verification and tool preparation gate the package checks. After production
verification, the axiom audit can still report independently of checker-tool
preparation. The report requires all seven recorded outcomes to succeed.
Individual checker steps can continue on error to collect feedback, so use
the **Verification** table to identify a failed check.

On a default-branch push with runner-local handoff, Test rechecks the archive
digest and uploads `cache-staging` after every check passes. With cross-runner
transfer, Build uploaded it for Test. Publish cache requires both jobs to
succeed and a staged archive from the same run. It checks the repository
and commit in `producer.json`. The release tag is `lean-native-<commit>`
and the asset name includes the platform, toolchain, run and attempt.
The first publication creates a prerelease without changing the latest release.
Later publication preserves an asset with the same name.

## Cache boundaries

| Object | Contents and reuse |
| --- | --- |
| Root checkpoint | Root working build and configuration outputs, including in-package test compilation. Immutable keys include context, ref, run, attempt and Build or Test suffix. |
| Dependency checkpoint | Working builds and generated configuration for all resolved dependencies. Keys use the compatible context and content generation. Build uploads a new generation on change or cache miss. |
| Tools checkpoint | Private lint runner, auditor build outputs and dependency outputs that differ from the current Build dependency manifest. It retains native executable and library files as well as module outputs. |
| `build-dependencies` | Complete same-run dependency closure for cross-runner Test. Layered Build reuses its compressed dependency checkpoint for transport, including dependencies restored without new compilation. |
| `cache-staging` | Native production archive for Test on the cross-runner path and for release publication. |
| `lean-native-<commit>` release asset | Producer mappings and native outputs for compatible consumers. The archive records the producer repository, commit, package and compiler. |

The checkpoint context includes the schema, platform, architecture,
`lean-toolchain`, resolved manifest and package configuration. The tools
context also includes lint adapter sources and the auditor pin. Root and tool
restore prefixes prefer the current ref, then a compatible seed visible
under GitHub's cache rules. Proof edits retain compatible prefixes, and Lake
checks the current inputs before reusing compilation. Different runner paths
can cause Actions cache misses even with matching key prefixes.

Layered checkpoints stream compressed working outputs and exclude checkouts
and the global content store. They omit reconstructible `*.setup.json` files
under the generated `ir` directories and retain traces, hashes and other
generated files. [checkpoint.py](ci-cache/checkpoint.py) verifies the archive
manifest, paths, sizes and content hashes before overlay, then rechecks content
during per-file atomic replacement. The replacement avoids mutating existing
cache hardlinks. A matching dependency generation can reuse the already
validated compressed archive.

The preflight requires both checkpoint helpers and a supported Lean 4.34.1
layout. The root uses the standard TOML and generated-directory layout.
Package overrides, external path dependencies and unsupported executable
dependency configs use legacy transport when detected at selection. Build
rechecks support after a broad restore. Jobs acquiring dependencies recheck
materialized configuration files before overlay. Failed checks at those
points stop the job before relying on the layered archive.

On a root or dependency checkpoint miss, layered Build can read a broad
legacy cache as a migration seed. Ordinary legacy runs restore and save
`.lake` and the native store together. For ordinary restores, the
legacy prefixes prefer the current toolchain and manifest and then allow
broader seeds for Lake to verify. The explicit promotion path requires its
exact seed. Layered jobs write scoped checkpoints. Optional Actions caches
warm compilation, while Test requires verification of this run's outputs
before saving layered Test progress.

Build writes `.lake/ci-cache/dependencies.json` as the tools checkpoint
baseline. Test obtains it from the retained workspace or the current
dependency overlay. Test saves the complete tool delta against that baseline,
including reused checker outputs. It skips unchanged tool uploads when a
compatible checkpoint already covers them. On the same host, Test also skips
uploading a root checkpoint when its generation equals Build's generation.
The [native cache guide](../docs/CACHING.md#local-reuse) covers local Lake
cache reuse.

### Published dependency seeds

Build discovers eligible `kangxyz/*` Git packages and exact pins from
`lake-manifest.json`, including inherited dependencies. The production
`-o` mapping covers the root package, so upstream packages have their own
published mappings. Build prefers `lean-native-<pin>` and considers at most
five matching assets, with fallbacks from the twenty most recent releases.
The tag must target the producer commit. Modern archives must match
`producer.json` and the platform and toolchain domain. Legacy asset names
are admitted as optional seeds, with current input checks left to Lake.

Build admits flat regular staging files and, in layered mode, verifies the
module archives before import. It registers them with
`lake cache unstage <staging-directory> <manifest-package-name>`, preserving
the package selector, then removes the temporary download. An unavailable
or incompatible seed leaves the ordinary incremental build available. The
workflow token reads public releases. The logs distinguish the actual
producer commit from the consumer's pin.

### Native staging and repair

The workflow checks root `.lake/build/ir` for read-only, runner-owned regular
`*.ltar.hash` sidecars before the first Lake command and again after cache
preparation on the applicable paths. It unlinks only those sidecars so
Lake can regenerate them without changing the permissions of cached
artifact inodes. In Lake 4.34.1, a reused module can still need an archive
and hash write when exporting mappings with `-o`. A `Replaying` heading can
therefore precede a new write failure.

For layered staging, [stage.py](ci-cache/stage.py) checks the mapping and
forces unpacking of every referenced module LTAR on disposable copies. When
it finds a malformed derived archive, it removes only the affected derived
files and references, guards the compiled bytes, and uses a metadata-only
`lake --no-build --rehash` export to repack. It validates the complete stage
again before packaging. The helper has a five-minute budget. Use the
seven-day `native-stage-validation` artifact for repair and failure details.

## Declaration-lint execution

CI uses the package's [.github/lint/run.sh](lint/run.sh) when present, which
forwards to the [packaged adapter](../scripts/README.md#native-check-invocation).
The adapter prepares a small executable under `.lake/lint-runner` against
the existing Batteries checkout. It runs
`lake --no-build --builtin-only lint <production-roots>` first and collects
the declaration driver's result even when builtin lint finds errors.
Its batched path schedules batches of 64 declarations across the worker pool,
applying all enabled checks to the full selected environments. It preserves roots,
options and suppressions. Compilation of the runner can be cached, and
every check invocation runs the declaration checks.

Preflight selects the native
`lake --no-build lint <production-roots> -- --trace` command for an
unsupported toolchain, provider or driver configuration. The worker count
is bounded by available CPUs and the local toolkit can impose a stricter
thread limit. CI uses a twenty-minute attempt with
`LEAN_ABORT_ON_PANIC=1` and a thirty-second kill grace. It retries only exit
124, once. The step has a forty-five-minute outer limit.

## Timeouts and recovery

The Build deadline is the effective job limit minus 30 minutes for cleanup
and checkpoints. Checkout, downloads and setup spend time before that
deadline. On EC2 the compiler receives the lesser of 180 minutes and the
remaining time. On the default hosted route it receives the remaining time
before the 330-minute cutoff. If preparation exhausts the window, the job
fails before launching Lake and skips new Build checkpoints.

GNU `timeout` sends SIGINT and allows 60 seconds before a forced kill.
Compiler failure and cutoff exits 124 and 137 fail Build and block Test
and publication. After an attempted layered Build, failed staging can
still leave completed root and dependency checkpoints once both recorded
scope stops succeed. Hard job cancellation, instance teardown and failed
cache delivery can prevent saving progress.

| Symptom | Where to look |
| --- | --- |
| EC2 job stays queued | Check the `workflow_job` webhook, matching labels, runner registration and the shared concurrency queue. |
| Test cannot claim the Build workspace | Compare runner, ref, commit, run ID and attempt in both jobs. Rerun all jobs to create a new handoff, including after a Test-only rerun would change the attempt number. |
| Compiler times out or fails | Inspect the Build outcome and checkpoint save steps. A new run on the same ref can resume from compatible completed work. |
| Archive verification or production readiness fails | Inspect `native-stage-validation`, the current-run stage and dependency transfer or claim steps, and the `--no-build --rehash` output. |
| Build passed but Test or publication did not | Inspect the **Verification** table, the archive upload step and the **Cache publication** summary. |

## Resource scopes and observations

Native run steps use named systemd scopes as the runner UID and GID.
Build and Test validate positive resource inputs, reserve 2,048 MiB of
physical RAM for the runner and OS, clamp the requested scope limit to
the rest, and disable scope swap. `LEAN_NUM_THREADS` controls Lake's runtime
pool. `CI_LINT_WORKERS` controls the accepted batched adapter. Aglib's
`-M12800 -j4` in `lakefile.toml` applies to its Lean frontends. The scope
also covers dependency and auditor processes, which may have their own
frontend options.

Each job records its own scopes under
`$RUNNER_TEMP/lean-ci-scopes/<run>-<attempt>-<job>/`. Cleanup runs outside
those scopes and synchronously stops only the units recorded for that job.
This settles descendants left alive by cancellation before staging or
saving reads their files. A failed required scope stop blocks the
corresponding archive operation.

The optional [resource sampler](ci-resource-monitor.py) records scalar JSONL
observations roughly every 15 seconds, bounded by the job lifetime and a
4 MiB output cap. Cleanup stops it with a file sentinel. The
`native-resources-<run>-<attempt>-<job>` artifact lasts seven days. Sampling
and delivery are best effort.

The summary reports observed cgroup memory charges, the largest individual
scope peak seen, and sampled simultaneous Lean processes. Host memory and
CPU metrics are separate fields. File-cache metrics can overlap, and
`lean_frontends` counts sampled processes independently of Lake's thread
pool size. For EC2, samples can also appear as `LEAN_CI_RESOURCE` lines in
`/var/log/user-data.log`, collected under
`/github-self-hosted-runners/aglib-ec2-pilot/user_data` in CloudWatch with
the instance ID as the stream.

## Branch promotion and regression tests

The [cache promotion workflow](workflows/cache-promotion.yml) is an
explicit, reviewed procedure for the pinned producer and target ref in
[promotion.py](cache-promotion/promotion.py). Its export, seed and readiness
phases bind the archive and producer metadata to an exact cache key and
version. `first-ci-cache` supplies the export run, metadata artifact ID,
metadata SHA-256 and exact seed key to the shared workflow. It selects
cross-runner transport, checks allowed source differences and resource
bounds, and requires the exact seed and native no-build readiness before
ordinary checks. The workflow's approval hold governs its use.

The [automation index](INDEX.md) lists the regression commands. The workflow
suite covers routing and gates. The [Linux checkpoint workflow](workflows/cache-checkpoints.yml)
exercises cold recovery, interrupted-build continuation and corrupt archive
repair with the pinned toolchain.
