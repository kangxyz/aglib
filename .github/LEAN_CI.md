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
  cache and incrementally builds only the production targets. It saves completed
  compilation, stages the production build's native mappings and outputs, and
  uploads that mathematical artifact for Test. It does not prepare checker tools
  or an auditor, run generated-entry or text-style checks, or build `check-targets`.
  Its final report requires the production build to succeed; checker failures
  belong to Test and do not change Build's result. Production Build is not retried.
- `test_lint` requires successful Build. It downloads this run's mandatory
  `cache-staging` artifact, overlays its native mappings/artifacts with
  `lake cache unstage --force-overwrite`, and verifies only the production targets
  with `LAKE_RESTORE_ARTIFACTS=true lake build --no-build --rehash`. A missing
  artifact or incomplete native output fails the job before checker preparation.
  This follows Mathlib's
  [same-run staging transfer and completeness check](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/.github/workflows/build_template.yml#L444-L479).
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
  cache reuses the checkout and incremental outputs. No auditor archive travels
  through Build. The auditor reads built production roots and their imported
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
  `--latest=false`; later runs append their asset to the existing release.

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
transport relies on trusted cache producers. The downloaded tar is removed after
native unstaging so subsequent cache saves do not duplicate it.
Release assets provide a separate manual download interface for local or remote
consumers; CI does not download these releases. Use `gh release download
lean-native-<commit> --repo <owner/repo> --pattern
lake-native-cache-<run>-<attempt>.tar`, extract into a fresh staging directory,
then run `lake cache unstage <staging-directory> Aglib` from the consumer package
(substitute the actual dependency name). Lake validates applicability during the
subsequent build.

The focused regression suite uses Python and PyYAML:
`PYTHONPATH=scripts python3 -m unittest discover -s scripts/tests -p test_lean_ci_workflow.py -v`.
The caller preserves each repository's workflow name and concurrency group.
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
