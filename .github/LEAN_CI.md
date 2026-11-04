# Lean CI

[Aglib's workflow](workflows/ci.yml) calls the [shared Lean workflow](workflows/lean-ci.yml)
with production target `Aglib`. Runs for the same ref queue in order. Normal
local development uses [`scripts/check.sh`](../docs/DEVELOPMENT.md#local-verification-and-ci)
for the same checks against an existing checkout.

## Runner routing

| Trigger | Build and verification | Publication |
| --- | --- | --- |
| Push to Aglib `main` | Separate Build and Test jobs on EC2 | Separate GitHub-hosted job after verification |
| Manual dispatch on `main`, profile `ec2` (default) | Separate Build and Test jobs on EC2 | Skipped |
| Pull request, push to another branch, or hosted dispatch | Separate Build and Test jobs on Ubuntu 24.04 | Eligible only on a default-branch push |

The EC2 autoscaler matches `self-hosted, linux, x64, aglib-ec2-pilot`
and caps the pool at one Linux x86-64 instance. Both jobs use 56 GiB for
native process groups and eight Lake runtime threads. Declaration lint uses
eight workers. Lake runtime threads and the frontend flags in
`lakefile.toml` are separate settings.

Aglib can opt into runner-local handoff with the repository variable
`AGLIB_EC2_SHARED_HOST=true`. Before enabling it, provision a runner service
that stays registered between jobs, retains the checkout, and exposes the
root-owned mode file `/etc/aglib-ci-runner-mode` with value
`aglib-ci-shared-host-v1`. The 240-minute Build and 90-minute Test limits
need a machine watchdog of at least 360 minutes including bootstrap.
Build renews the host timer before compiling. Keep the watchdog and runner
mode in the Terraform configuration. The [manual EC2 probe](workflows/ec2-pilot.yml)
shares the main workflow's queue and checks the runner's OS, disk, tooling
and network. Its optional second job verifies the runner and workspace
before enabling the production variable.

When the repository variable is unset, Build and Test use the transfer path.
Enable runner-local handoff only after the two-job EC2 probe succeeds.

The normal workflow routes PRs to hosted runners. GitHub assigns self-hosted
jobs by requested labels and groups. If external contributions expand, the
repository's Actions settings can require approval for all outside-contributor
workflows. Review their workflow changes before approval, and verify the
autoscaler's event and repository filters as part of tightening admission.
See [GitHub's self-hosted runner security guidance](https://docs.github.com/en/actions/reference/security/secure-use#hardening-for-self-hosted-runners).

## Execution order

1. **Prepare.** Build checks out the selected revision, restores optional
   checkpoints, resolves the pinned Lean toolchain, obtains the Mathlib cache,
   and applies the working-build checkpoints. In runner-local mode it applies
   the optional tools checkpoint before the dependency and root checkpoints.
2. **Build and checkpoint.** Run `lake build --rehash` for the production
   targets and emit native output mappings. Quiesce the job's compiler scopes,
   validate and stage the native publication archive, then save completed root
   and dependency compilation independently of later checks.
3. **Hand off and verify.** With runner-local handoff enabled, Build leaves its
   checkout, native cache, toolchain path and stage on the runner. Test checks
   the runner name, repository, commit, run and attempt before reusing them.
   It verifies the local publication archive against an isolated root and empty
   native cache, then restores the original working build for its checks.
   In the transfer path, Test fetches the pinned dependency sources and restores
   the complete dependency closure and native root artifact from its own run.
   Both paths require `lake build --no-build --rehash` to succeed before checks.
4. **Check and publish.** Test runs generated-entry checking, Mathlib text style,
   `lake test`, declaration lint and the pinned production axiom audit.
   With local handoff, Test uploads the unchanged publication stage after
   the checks pass on a default-branch push. Only after both jobs succeed
   does the separate hosted publisher verify the stage's producer repository
   and commit and publish an immutable asset under `lean-native-<commit>`.

The [packaged lint adapter](../scripts/README.md#native-check-invocation) runs
builtin lint and the configured declaration driver over all production roots.
The declaration lint step retries once after exit 124 and has a 45-minute
outer limit. The axiom audit is independent of checker-tool preparation and
permits `propext`, `Classical.choice` and `Quot.sound` in the production closure.

## Timeouts and recovery

The deadline starts before checkout. On EC2 the compiler receives up to
180 minutes, capped by the remaining time before the 30-minute checkpoint
reserve. The hosted Build default is 360 minutes with the same reserve.

At the compiler cutoff, GNU `timeout` sends SIGINT and allows 60 seconds for
shutdown. A failed or timed-out compiler still permits checkpoint saves after
its recorded scopes stop. Preparation that never launches the build command
cannot save a new compilation checkpoint. Rerun on the same ref to resume
from a compatible checkpoint. In runner-local mode, rerun all jobs if Test
reports that the Build workspace is unavailable. A new attempt needs its own
handoff identity and publication stage.

Use the run's Production build and Verification tables to identify the failed
stage. The best-effort Resource observations table and `native-resources-…`
artifact record sampled cgroup metrics. EC2 also mirrors samples to its existing
CloudWatch user-data log. For an EC2 job stuck in the queue, inspect the
`workflow_job` webhook delivery, matching labels, and runner registration in
that order.

## Cache boundaries

| Object | Purpose |
| --- | --- |
| Root and dependency checkpoints | Warm incremental compilation across runs. Root saves have distinct Build and Test keys. Dependency archives reuse compatible content generations. |
| Tools checkpoint | Private lint and auditor outputs, plus dependency files that differ from the current Build dependency manifest. |
| `build-dependencies` | Complete current-run dependency closure sent only on the cross-runner transfer path. |
| `cache-staging` | Validated native production archive sent to publication and to Test on the cross-runner path. |
| GitHub release asset | Native producer output for compatible consumers, with producer commit and platform identity. |

The scoped checkpoints save generated working files and omit reconstructible
`*.setup.json` files. Lake checks compatibility against the current checkout.
With runner-local handoff, the Build dependency pack records the local manifest
used by the tools checkpoint. The post-check root save skips a second upload
when its content generation equals the Build generation.

The shared workflow retains legacy transport for unsupported layouts and the
explicit `first-ci-cache` promotion path. Promotion uses split Build and Test
jobs and separate resource checks. The [cache guide](../docs/CACHING.md)
explains local reuse, and [`checkpoint.py`](ci-cache/checkpoint.py) and
[`stage.py`](ci-cache/stage.py) own the archive formats and integrity checks.
