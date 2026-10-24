> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#investigating-lean-compilation-performance) · [Context](original-context.md) · [Case index](README.md) · [Next record](repair-workflow.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

# Investigating Lean compilation performance

This guide separates measured Aglib bottlenecks from candidate explanations and
records primary-source methods for investigating them. The compatibility basis
is Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. External issue states were checked on
2026-10-16. Historical reports do not establish a defect in the pinned compiler.
[Caching](../CACHING.md) owns artifact reuse; this guide concerns the cost of
checking a declaration when compilation is necessary.

