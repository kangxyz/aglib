# Minimal Mathlib-style CI

The template is adapted from Mathlib `d13f23b7`'s
[build_template.yml](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/.github/workflows/build_template.yml).
Callers supply only the Lake package directory and production targets.

- `build` configures the pinned toolchain, restores cache and calls `lake build`.
  Native setup follows Mathlib's pinned
  [setup-build-env action](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/.github/actions/setup-build-env/action.yml#L85-L103):
  the official `https://elan.lean-lang.org/elan-init.sh` installer and `elan which
  lake` select the package's unchanged `lean-toolchain`. Installer download
  retries and at most three native toolchain-acquisition attempts handle
  transient failures. Exhausted retries or failed Lean/Lake version checks fail
  setup.
  Completed compilation is cached even when a later operation fails.
  Mathlib's `mk_all --lib <root> --check` verifies the generated production
  entries after compilation has been saved. It never rewrites sources in CI.
- `test_lint` requires successful Build and generated-entry checks. It starts
  by downloading this run's mandatory `cache-staging` artifact,
  overlaying its native mappings/artifacts with `lake cache unstage
  --force-overwrite`, and verifying all production roots and lint executables
  with `LAKE_RESTORE_ARTIFACTS=true lake build --no-build --rehash`. A missing
  artifact or incomplete native output fails the job before Test/lint/audit.
  This follows Mathlib's
  [same-run staging transfer and completeness check](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/.github/workflows/build_template.yml#L444-L479).
  It then runs `lake test` and
  `lake --no-build lint <production-roots> -- --trace`. Library Tests use incremental compilation; persisted
  compiler-linter diagnostics are reused. Batteries declaration lint keeps its
  ordinary package-wide behavior. A failed Test does not suppress lint feedback.
  `lake --no-build exe mathlib/lint-style <production-roots>` separately runs
  Mathlib's own text checks over the full import lists without automatic fixes. No Git
  diff, explicit file list or library-specific style driver filters the scan.
  The [axiom auditor used by lean-action](https://github.com/leanprover-community/axiom-audit/tree/46024e005996495c65ef609368e11ab39c4222e3)
  reads the built production roots and their imported closure; only `propext`,
  `Classical.choice` and `Quot.sound` are allowed. It does not compile the project
  or replay proofs. Deliberate negative Test fixtures are outside this audit.
- `upload_cache` publishes staged native compilation only after Build,
  generated-entry, Test, lint, text-style and production-axiom checks all pass,
  and only for trusted default-branch pushes. Failed or interrupted Build/Test
  work retains the always-run Actions cache saves where the runner can finish
  cleanup; this does not authorize release publication.
  First publication creates the release together with its asset and
  `--latest=false`; later runs append their asset to the existing release.

Necessary host adaptations are explicit: GitHub-hosted runners replace Mathlib's
self-hosted pool; GitHub caches/releases replace its Azure backend; native
`lake cache stage` replaces its project-specific cache staging executable.
Library and Test drivers live in Lake configuration. The Build job prepares the
Batteries, Mathlib text-style and `mk_all` executables; final checks use
`--no-build` to prevent hidden compilation. Generate each production entry with
`lake exe mathlib/mk_all --lib <root>`. Both native lint commands receive the
full production roots from `BUILD_TARGETS`, before `--` for `lake lint`. This
keeps builtin lint and Mathlib's text driver working when disjoint source
libraries have `roots = []`, leaving no default roots to infer. Mathlib's text
driver scans each selected root's complete import list without changed-file
filtering. Test libraries use `TestName.+` globs and `lake test`;
they are not default production targets and have no generated `TestName.lean`.
All four callers use these same native mechanisms.
Native setup runs from the caller's Lake package directory. Configure Lean
or cache-restore failure suppresses checks requiring compiled outputs; Test
failure still allows lint, text-style and axiom feedback before the final report
fails the job. The focused workflow regression suite uses Python and PyYAML:
`python3 -m unittest discover -s scripts -p test_lean_ci_workflow.py -v`.
The caller preserves each repository's workflow name and concurrency group.
`cancel-in-progress: false` with `queue: max` serializes runs without cancelling
the running job or replacing an already pending run.

Each job restores `.lake` and the native cache directory together once. Build
and Test run on separate runners and each saves its completed compilation,
including partial progress on failure. Test's Actions restore warms unchanged
dependency outputs; it is not the Build-to-Test handoff. Lake's `-o` mappings
include root-package outputs, so the warm cache also supplies the Mathlib and
Batteries executables built by Build. The required current-run artifact then
overwrites root-package cache mappings. The no-build check tests availability
and applicability of the combined warm and current-run outputs against native
inputs; it does not certify cryptographic provenance or integrity of cache
bytes. As in Mathlib, this transport relies on trusted cache producers.
The downloaded tar is removed after native
unstaging so subsequent cache saves do not duplicate the archive. Release
assets provide a separate
manual download interface for local or remote consumers; CI does not download
these releases. Use `gh release download lean-native-<commit> --repo <owner/repo>
--pattern lake-native-cache-<run>-<attempt>.tar`, extract the archive into a fresh
staging directory, then run `lake cache unstage <staging-directory> Aglib` from
the consumer package (substitute the actual dependency name). Lake validates
cache applicability against current native inputs during the subsequent build.

Nightly automation, PR labelling, bibliography checks, style-fix bots, downstream-client
jobs and the old Python orchestration are outside this minimal template.
Mathematical review and kernel replay retain their separate existing owners.
