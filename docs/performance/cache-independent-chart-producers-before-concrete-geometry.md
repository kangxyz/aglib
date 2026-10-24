> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#cache-independent-chart-producers-before-concrete-geometry) · [Context](original-context.md) · [Case index](README.md) · [Previous record](specialize-the-whole-arc-argument-after-fixing-its-algebraic-data.md) · [Next record](construct-the-tensor-comparison-inside-the-shared-chart-witness.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Cache independent chart producers before concrete geometry

When one concrete specialization blocks an incoming module, use its real
mathematical interfaces to separate independent producers. In the blowup
presentation, [ChartMap](../../Aglib/AlgebraicGeometry/Blowup/ProjectivePresentation/ChartMap.lean),
[RowCoordinates](../../Aglib/AlgebraicGeometry/Blowup/ProjectivePresentation/RowCoordinates.lean)
and [DegreeOneAugmentationChart](../../Aglib/AlgebraicGeometry/Blowup/ProjectivePresentation/DegreeOneAugmentationChart.lean)
were separated from the scalar Rees specialization. The original namespaces,
actual maps and mathematical conditions were retained. Private coefficient
and preimage data stayed private; only the actual current consumer interfaces
were exported. The native Lake graph can retain each successful producer
when another module fails.

Run `remote-1b573df8ede942709d4c67dd6437e52e`, source snapshot
`aad4d3dd3fa636465cf368351715da01715d27f8fd2a0a9132ceb39cbbdd16bf`,
compiled ChartMap source `9e9765f2` in 3.4 seconds, RowCoordinates source
`9341ad2b` in 197 seconds and DegreeOneAugmentationChart source `4afe0736`
in 4.5 seconds, all at default budgets. ScalarChart failed separately;
its concrete consumer, embedding and final contraction theorem were not
covered. These are scoped reusable successes, not a completed-contraction
claim. Source and proof changes differ from the predecessor monolith,
so these measurements do not establish a controlled runtime improvement.
No standalone extra check, replay, client or profiling stage was added.

