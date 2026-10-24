> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#declaration-lint-memory-in-ci) · [Context](original-context.md) · [Case index](README.md) · [Previous record](values-at-concrete-fibre-products-over-spec-commringcatof-a.md) · [Next record](principal-chart-pasting-at-the-ci-memory-budget.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Declaration lint memory in CI

On 2026-10-19 the CI job for `c6bddf7` was killed by the resource guard (exit 137, RSS cutoff
13,824 MB) about six seconds into the Batteries declaration linter, after Lake's builtin lint
phase had finished. The previous push, `9645827`, passed the same step. CI ran both phases as one
guarded `lake lint -- --no-build`. Measured separately on the remote Linux builder at `df4680e`,
the builtin phase (`lake lint --builtin-only`, which loads the `Aglib` and `AglibTest`
environments in the Lake process) peaked at 8.7 GB and the driver (`runLinter --no-build Aglib`)
at 6.4 GB. A candidate explanation, consistent with these numbers: the Lake process keeps the
builtin phase's imported environment mapped while it runs the driver, and the guard sums the
resident memory of its process group, so the library's growth by a few dozen modules moved the
sum past the cutoff. CI now runs the builtin phase and the driver as separate guarded processes.
Keep separately guarded commands for phases that each load the whole library.

A standalone full-library timing on 2026-10-20 used source `4282748`, Lean 4.34.1,
and existing local macOS artifacts for 2,128 production files plus the `Aglib`
root. `lake --no-cache --rehash --no-build build Aglib` first verified the native
graph in 13.17 seconds without compilation. Running Batteries separately as
`lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build Aglib`
then passed in 144.34 seconds, with 6.32 GiB peak owned-process-group RSS, one
Lean thread, a 12,800 MiB frontend cap and a 13,824 MiB group cutoff. Both guards
reported successful process-group closure. This measures the declaration pass;
builtin lint, standalone text style and axiom audits are separate costs. A
seven-origin isolated declaration run had taken 44.72 seconds at 4.51 GiB;
repeated environment loading means its per-origin average does not predict a
single full-library pass. Whole-environment and exact-origin lint coverage also
retain their distinct environment/policy premises.

Under the same cached source and limits, full builtin lint took 17.39 seconds
at 3.55 GiB for `Aglib` and 13.63 seconds at 4.49 GiB for `AglibTest`. The fixed
auditor over origin prefixes `Aglib` and `AglibTest` passed for 35,401 declarations
in 15.62 seconds at 5.72 GiB, including its 16 private/generated controls. The
positive-test cache-only graph check took 6.42 seconds. These measurements
support batching and separate processes rather than a new result-cache system.

An initial whole-`AglibTest` Batteries declaration pass took 15.71 seconds
at 5.47 GiB and exposed 30 existing issues: 21 definition names, five missing
docstrings and four deliberately specialized unused instance arguments. The
cleanup renamed the definitions, added the documentation and explicitly named
the intentionally unused regression instances with leading underscores, as the
pinned linter permits. Statement types, hypotheses and proof bodies were
preserved. Only the 18 changed test leaves and their umbrella were recompiled.
The complete test declaration pass then succeeded in 15.86 seconds at 5.46 GiB;
changed-source style, test builtin lint, the full origin audit and rejection
controls also passed. CI now runs this test umbrella pass once alongside the
production declaration pass, with their separate environment predicates.

