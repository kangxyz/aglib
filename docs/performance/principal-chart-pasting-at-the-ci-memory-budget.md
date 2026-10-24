> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#principal-chart-pasting-at-the-ci-memory-budget) · [Context](original-context.md) · [Case index](README.md) · [Previous record](declaration-lint-memory-in-ci.md) · [Next record](ambient-chart-pasting-and-affected-consumers.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Principal chart pasting at the CI memory budget

CI runs [39102309068](https://github.com/kangxyz/aglib/actions/runs/39102309068)
and [39108321624](https://github.com/kangxyz/aglib/actions/runs/39108321624)
failed in `principalWholeChartPaste`, at the native 12,800 MiB limit. The
previous local pass at a higher limit did not establish fit for CI.

The retained [Principal](../../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Canonical/ModelCharts/Principal.lean)
uses one private `WholeChartPasteData` value and six typed supplier equations.
The final categorical paste consumes those same projections instead of
reconstructing the concrete chart endpoints together. The original public
statement, chart arrows and supplier equations are unchanged.

Fresh local macOS compiles at the unchanged 12,800 MiB native limit passed
with one and four compiler threads. The four-thread check took 408.9 seconds
and peaked at 12,918.8 MiB process-group RSS, below the 13,824 MiB guard.
Its six comparable native artifacts matched the one-thread build exactly.
Scoped declaration, text-style and source-policy checks passed. These local
measurements do not give a controlled speedup ratio. The subsequent Linux
CI run [39115201867](https://github.com/kangxyz/aglib/actions/runs/39115201867)
passed the repaired Principal in 625 seconds, then exposed the same native
memory limit in `ambientWholeChartPaste` at `Ambient.lean:612`.

