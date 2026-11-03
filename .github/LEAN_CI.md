# Minimal Mathlib-style CI

The template is adapted from Mathlib `d13f23b7`'s
[build_template.yml](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/.github/workflows/build_template.yml).
Callers supply the Lake package directory and nonempty production `build-targets`.
An optional `check-targets` string, empty by default, names extra helper targets
that Test builds alongside its checker tools. It never changes Build's targets
or mathematical artifact. For example, a caller can build `R5Lab Essays` in
Build and supply `Checks` separately as a Test helper.

The reusable workflow defaults to GitHub-hosted Ubuntu 24.04. Optional
`runner-labels` is a JSON array encoded as a string (default
`["ubuntu-24.04"]`); `native-memory-mib` (13824), `lake-threads` (1) and
`lint-workers` (2) select Build/Test resources. `job-timeout-minutes` defaults
to 360 and sets both job limits. Optional `build-lake-threads` defaults to 0,
which retains `lake-threads`; a nonzero value overrides only the production
Build step's Lake runtime pool. Other Build steps and all Test/lint steps retain
`lake-threads`. Publish cache always retains its hosted runner and historical resources.

Aglib routes automatic pushes to `main` to the repo-only ephemeral EC2 pool.
Manual dispatch defaults to `runner-profile=ec2`; an explicit `hosted` choice
uses GitHub-hosted resources. Pull requests, pushes to other branches and all
non-main dispatches remain hosted. EC2 jobs use exactly
`["self-hosted","linux","x64","aglib-ec2-pilot"]`, 57344 MiB aggregate native
memory, four Lake runtime threads outside production Build, and four lint workers.
Automatic main pushes use 90-minute Build/Test limits and eight production Build
Lake runtime threads. EC2-only manual choices `ec2-job-minutes` (`90` by default,
or `150`) and `ec2-build-lake-threads` (`8` by default, or `4`) permit longer jobs
or the smaller Build runtime pool. Missing or unexpected EC2 choice values use
90 minutes and eight Build Lake runtime threads; automatic pushes ignore manual
choices. The 30-minute cache margin leaves a 60- or 120-minute compiler budget.
Lake runtime threads do not specify frontend process concurrency or change the
`-j4 -M12800` frontend arguments. Other EC2 steps and Test/lint retain their
existing runtime and worker settings; shared reusable workflow defaults remain
hosted and unchanged.

Automatic main pushes incur on-demand AWS charges. USD 5 is the current trial
budget, not a billing hard cap. The pool uses Ubuntu 24.04 Linux x86_64 on
`m7i.4xlarge` (16 vCPUs, 64 GiB), allows at most one VM, and terminates each runner
after one job. Build and Test therefore use separate ephemeral runners. The
machine watchdog must exceed the selected job limit plus bootstrap time; that
infrastructure setting is managed separately from this template.

Optional Actions caches can miss across hosted and EC2 runners because cache
versions include raw path strings and their temporary directories differ.
The existing migration restore remains available when a compatible cache exists;
a miss falls back to the ordinary incremental/cold build and compatible upstream
caches. Current-run dependency and root artifacts remain mandatory for Test.

`LAKE_NO_CACHE=true` follows Mathlib by disabling automatic package build
downloads from Reservoir/GitHub. This is separate from
`LAKE_ARTIFACT_CACHE=true`, which keeps native project artifacts available.

- `build` restores caches, configures the pinned toolchain, obtains the Mathlib
  cache, imports published native caches for resolved `kangxyz/*` Git dependencies,
  and incrementally builds only the production targets. It saves completed
  compilation, stages the production build's native mappings and outputs, and
  uploads that mathematical artifact for Test. Callers containing
  both `.github/ci-cache/checkpoint.py` and `.github/ci-cache/stage.py` use the
  layered transport described below when the support preflight succeeds:
  completed root and dependency working outputs are saved separately, and a
  complete same-run dependency closure accompanies the root artifact.
  Other callers retain the legacy compressed native-store dependency fallback.
  Build does not prepare checker tools
  or an auditor, run generated-entry or text-style checks, or build `check-targets`.
  Its final report requires the production build to succeed; checker failures
  belong to Test and do not change Build's result. Production Build is not retried.
  The first step validates `job-timeout-minutes` as an integer greater than 30
  and records a compiler deadline that many minutes minus 30 after the Build job
  starts (330 minutes by default), including checkout, cache restoration, setup
  and dependency downloads.
  Production Lake receives only the time remaining, through GNU `timeout` with
  `SIGINT` and a sixty-second kill grace period. An already expired deadline
  skips Lake; timeout exit 124 or forced-kill exit 137 fails Build, so Test and
  Publish cache do not run. The job limit defaults to 360 minutes, reserving thirty
  minutes for the existing cache save and partial-output staging. Cache saving
  still runs after compiler failure or cutoff. On the layered path, bounded
  native staging repairs derived archives before root checkpoint packing. Both completed
  root outputs and completed dependency outputs have independent always-run
  checkpoints on the layered path. A later run on the same branch restores
  compatible saved outputs and continues incrementally;
  no automatic rerun is scheduled. Network failures or runner teardown can still
  prevent cache delivery.
- `test_lint` requires successful Build. It downloads this run's mandatory
  `cache-staging` artifact, overlays its native mappings/artifacts with
  `lake cache unstage --force-overwrite`, and verifies only the production targets
  with `LAKE_RESTORE_ARTIFACTS=true lake build --no-build --rehash`. A missing
  artifact or incomplete native output fails the job before checker preparation.
  This follows Mathlib's
  [same-run staging transfer and completeness check](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/.github/workflows/build_template.yml#L444-L479).
  Layered Test always downloads Build's complete same-run dependency snapshot,
  including unpublished outputs restored by Build even when no new dependency
  file compiled. It fetches pinned dependency source checkouts with `lake env true`
  without compiling the Mathlib cache executable, applies optional root/tool
  checkpoints, then overlays the mandatory current dependency closure and current
  root artifact in that order. Legacy callers recover the native-store snapshot
  only after an optional Actions cache miss or restoration failure. All recovery
  precedes the mandatory current-run root overlay. Successful output verification,
  rather than a warm-cache outcome, enables
  the later checks.
  Test then incrementally builds the Batteries declaration-linter, Mathlib
  text-style and `mk_all` executables plus any `check-targets`, using its restored
  caches. Mathlib's `mk_all --lib <root> --check` verifies the generated production
  entries without rewriting them; `lake --no-build exe mathlib/lint-style
  <production-roots>` scans the full import lists without automatic fixes.
  Both source checks collect feedback when checker preparation succeeds.
  Test also runs `lake test` and declaration lint. A caller containing
  `.github/lint/run.sh` forwards to the shared packaged adapter in
  `scripts/lean_tools/_lint/`; other callers retain
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
  the package's unchanged toolchain. When a scoped tool cache restores build
  outputs without source, CI clones the pinned checkout into an empty temporary
  directory, verifies its revision, then overlays source and `.git` while
  preserving the restored `.lake` outputs. A cold cache builds it there; a warm
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

Necessary host adaptations are explicit: selectable hosted or repo-only EC2
runners replace Mathlib's self-hosted pool; GitHub caches/releases replace its
Azure backend; native
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

Build and Test run on separate runners. The layered helper keeps three scoped
compilation caches, without saving dependency checkouts, the entire `.lake`
directory or the global native content store:

- Dependencies contain complete resolved dependency working build directories
  and Lake configuration outputs. Compatible immutable generations use the
  compiler, OS, architecture, manifest and configuration context plus a content
  generation. Build saves a generation only when content changed or the optional
  dependency cache was missing. Completed partial dependency work is saved after
  failed or interrupted Build as well as successful Build, once the production
  Build step actually starts. Earlier setup/acquisition failures do not replace
  a downloaded checkpoint with config-only state.
- Root checkpoints contain the root package's complete working build/configuration,
  including in-package test compilation. Branch/run/attempt keys let later runs
  resume partial progress; Test saves its additions under a distinct job suffix.
  Root and tool restores prefer the current branch, then a context-compatible
  seed within GitHub's existing cache visibility, including the default branch.
  Test saves root/tool progress only after successful production readiness;
  earlier source acquisition, overlay or readiness failures preserve prior caches.
  These checkpoints never authorize Test or publication.
- Tool checkpoints contain the private packaged lint runner, the pinned auditor,
  and dependency build/configuration additions or changes relative to the
  mandatory current Build dependency manifest. Each generation records that full
  difference, including already restored checker outputs. It retains actual
  native objects, libraries, executable and module facets through scoped working
  outputs rather than assuming module archives contain native executables.
  Unchanged tool content with a matched optional cache is not uploaded again.
  It saves compilation only; full lint and the existing check set still execute.

Scoped checkpoints omit only generated `*.setup.json` files under each actual
`.lake/build/ir` directory. Pinned Lake regenerates this compiler scaffolding
before compilation; native cold recovery and interrupted-build resume tests cover
its omission. Other JSON, traces, hashes and compiled native outputs remain.

All optional restores precede the mandatory current dependency and root overlays.
The current root `-o`/stage artifact and exact `--no-build --rehash` success remain
Test's authority. The dependency handoff reuses the complete compressed scoped
checkpoint; it is never reduced to newly compiled files. A current dependency
manifest also supplies the comparison basis for Test's tool checkpoint.
Archives use streaming zstd compression, and unchanged dependency generations
reuse compatible restored transport where supported by the helper. Network
failure or runner teardown can still prevent delivery; packing begins only after
this job's recorded compiler scopes have stopped.

The helper's conservative `supported` preflight selects layered caching only when
both helper files are present and the Lean 4.34.1 resolved layout is supported. Package overrides, external path dependencies and
unsupported layouts retain the legacy path. Build rechecks support immediately
after a broad migration restore so restored overrides fail before compilation.
Both jobs then run `supported --materialized` after dependency acquisition and
before checkpoint overlays. This checks the actual resolved dependency configuration
files and generated-directory layouts, including pinned known executable configs.
The first layered cache miss may read an existing broad cache as a migration
seed. Layered runs never save that broad format or delete old remote entries.
Callers without the helper and runs supplying `first-ci-cache` retain the legacy
restore/save and promotion gates; those jobs restore `.lake` and the native cache
directory together. Test's optional caches never substitute for the current
Build artifact. Compiler/platform/configuration contexts isolate incompatible
checkpoints, with tool source and auditor pin included in tool context.

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
removed after restoration so subsequent cache saves do not duplicate them.
The legacy dependency snapshot transfers the existing native content store,
using streamed zstd compression, and is skipped on a matching Test cache hit.
The layered dependency snapshot is mandatory regardless of optional cache hits.
Layered native staging validates every module LTAR by forced unpack into scratch.
If a cached derived archive is malformed, the helper selectively removes that
archive and its derived cache copy, then uses native `--no-build --rehash` export
to repack completed compilation. It revalidates the entire stage before transport
packaging; the repair has a five-minute budget and does not rebuild proofs.
A second recorded-scope stop precedes checkpoint packing, including after failed
staging. Failed validation still permits completed root/dependency checkpoints
once both scope stops succeed, while the failed job prevents Test/publication.
Optional published dependency seeds receive pure archive verification before
layered import; invalid candidates are skipped without changing remote releases.
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
default aggregate allowance is 13824 MiB. Build/Test validate all three resource
inputs as positive integers before opening a scope, and clamp the requested
memory to physical RAM minus a 2048 MiB runner/system reserve. Hosts without
that reserve fail before launching native work. Swap is disabled for that
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
Build/Test pass `lake-threads` as `LEAN_NUM_THREADS` and `lint-workers` as
`CI_LINT_WORKERS`; defaults retain the historical runtime pool of one and two
lint workers. The lint adapter still caps workers to the available CPUs.
The available CPU count is logged separately. Lake's runtime setting does not
promise a particular number of simultaneous compiler processes. Ordinary failure
can still execute the existing cache saves; VM/runner teardown remains outside that guarantee. The retired manual cache-client workflow is no longer present.

When the caller includes `.github/ci-resource-monitor.py`, Build and Test start
an optional Python sampler immediately after checkout with explicit `shell: bash`,
outside the native compilation scopes. It inherits Actions process tracking and
also exits at the job's configured lifetime (at most 12 hours), a stop sentinel,
or a 4 MiB output limit. It writes one scalar-only JSONL observation about every
15 seconds under `$RUNNER_TEMP/lean-ci-resources/<run>-<attempt>-<job>/`.
Cleanup requests a stop using that private directory, without signaling any PID.
It runs after the existing cache saves and uploads a uniquely named
`native-resources-<run>-<attempt>-<job>` artifact with seven-day retention. Start,
stop and upload are best effort and never gate mathematical checks or publication;
callers lacking the helper skip sampling. Runner teardown can prevent delivery.

Samples distinguish host `MemTotal`/`MemAvailable` from native cgroup charges.
They sum `memory.current`, `anon`, `file`, `inactive_file` and `file_mapped` only
across this job's disjoint recorded scope roots; parent counters already include
descendants, whose memory counters are never summed again. File counters overlap:
`file_mapped` and `inactive_file` help describe charged file cache but do not
measure a working set and must not be added to `file`. These are cgroup memory
charges, not sums of process RSS. `native_memory_peak_max_bytes` is the largest
individual live scope's kernel `memory.peak` observed at that sample, not the sum
of scope peaks or a guaranteed whole-run maximum. Scalar readable-scope counts
make missing metrics explicit. Host CPU busy percentage and native CPU-core use
come from counter deltas; native deltas require a scope present in consecutive
samples. Lean frontend concurrency counts live runner-owned `lean` executables
in the scopes' recursive process membership, deduplicating PIDs; it counts
processes, not runtime threads or CPU-runnable states. Short-lived processes and
collected scopes between samples can be missed. The job summary reports observed
coverage, and records no environment, command lines, source contents or secrets.
For the exact `aglib-ec2-pilot` runner label only, the sampler also mirrors each
scalar line with prefix `LEAN_CI_RESOURCE` to the existing regular, nonsymlink
`/var/log/user-data.log`, using noninteractive `sudo tee -a` with a one-second
timeout. The EC2 pool already collects that file in CloudWatch log group
`/github-self-hosted-runners/aglib-ec2-pilot/user_data`, stream `<instance_id>`,
so existing AWS log reads can observe future jobs live. The helper never creates
or changes permissions on a root log, adds no services or permissions, and disables
the mirror after an unavailable file, append failure or timeout. Hosted callers
skip mirroring; artifact and summary delivery remain independent of it.

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

The shared adapter in `scripts/lean_tools/_lint/` uses the package's existing
toolchain and Batteries APIs. `.github/lint/run.sh` is its CI forwarding entry;
local `scripts/check.sh`, installed `lean-tools check` and `--list` select the
same packaged implementation. It backports the full-scope worker scheduler from
[Batteries PR #2026](https://github.com/leanprover-community/batteries/pull/2026).
The pinned old implementation creates a task for each declaration/linter pair;
the adapter assigns batches of 64 declarations to a bounded worker pool and
retains only reported failures. Every enabled linter, including slow linters,
still checks the complete original declaration set in the full imported root
environment. The adapter does not filter changed modules or cache lint results.
The local toolkit also always executes declaration lint, including custom
linters that may consume external state. Other checks retain their existing
compatible-result reuse, as described in the
[toolkit guide](../scripts/README.md#input-identity-and-reusable-results).

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
compilation and the existing Actions cache reuse the executable; every adapter
execution runs the declaration checks. Local checker preparation establishes
the private generated sources and binary before observing lint inputs.
The private tool build explicitly selects its
generated TOML and refreshes only that tool's dependency resolution while keeping
the package toolchain. Restored tool configuration or path entries cannot select
a different executable or provider. As in
[Batteries PR #2028](https://github.com/leanprover-community/batteries/pull/2028),
the imported environment is marked persistent only when there is exactly one
resolved declaration-driver root; multiple roots keep ordinary release behavior.

The adapter defaults to two workers, capped by the process's available CPUs.
`CI_LINT_WORKERS` selects another positive count, with the same CPU cap. The local
guarded toolkit also enforces the admitted per-process thread budget, which can
be lower than the compiler job count; its normal local budget permits one worker.
The guard supplies that authoritative cap even if an inherited lint setting
requests more workers. The worker setting applies only after preflight accepts
the adapter. Build, Test
and unsupported native fallbacks retain their existing resource settings and
job scopes. Unsupported toolchains, provider
versions or driver configurations execute the original configured
`lake --no-build lint <production-roots> -- --trace` command. Preflight makes that
decision before the adapter imports the dependency API, including root package
overrides and competing root/provider configurations. Production Lake
configuration and dependency pins remain unchanged.

The existing twenty-minute attempt limit, retry policy, final Test report and
Publish cache gate still require the complete current checks to succeed.
