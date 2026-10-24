> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#retain-the-original-pullback-row-equation-boundary) · [Context](original-context.md) · [Case index](README.md) · [Previous record](preserve-both-affine-unit-comparisons-in-tensor-section-transport.md) · [Next record](keep-the-completed-stalk-equation-through-specialization.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Retain the original pullback-row equation boundary

On the same Lean 4.34.1 / Mathlib `d13f23b7` basis, the concrete affine
restriction specializations in
[Restriction](../../Aglib/AlgebraicGeometry/Blowup/ProjectivePresentation/Restriction.lean)
reached the default 200000-heartbeat `whnf` limit in both the quotient-cube
and framed original-row comparisons. Native run
`remote-72c0dd0ea2924206b5b28e7bf3d821ef` records those two failures. The
abstract cube argument alone did not prevent expensive conversion when its
result was pasted into the actual sheaf/module pipeline.

Use the same regular `QuotientRestrictionEq` and `RowRestrictionEq`
constructors in both the generic producer and concrete consumer. Their
arguments are the actual module objects, frame comparisons, quotient maps
and original sections. The concrete proof supplies established equations
for those arguments; it introduces no extra mathematical hypothesis.
Keep naturality at the exact component heads `(E.app M).hom` and
`(E.app D).hom`. A small typed `framed_naturality_paste` lemma composes
that equation with the original unit/frame/quotient arrows without asking
a final concrete rewrite to reconstruct their representations.

Restriction source
`fe89dc56d4a309ae3cae6d48b05cd7e0fdd2975a2c0cdfcdcf5477b4bab72b80`
passed ordinary native compilation in 301 seconds in
`remote-0cb9da7407c44157992bcd73c41985b2`, source snapshot
`577d7825be362af684667e2e6858ca1db5a6926544e93a794d8d86121c974de4`.
Default budgets, original maps and full ideal were unchanged. The outer
graph failed separately in ChartCoordinates, so this evidence covers
Restriction and its original row equation, rather than the complete
projectivity or contraction theorem. No profiling or extra replay was
performed. Different source repairs and cache states preclude a controlled
timing comparison or a general compiler-cause claim.

