> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#short-complex-colimit-comparisons-normalize-abstract-endpoints-first) · [Context](original-context.md) · [Case index](README.md) · [Previous record](typed-projection-proofs-across-additive-hom-carriers.md) · [Next record](additive-ext-transport-avoid-an-irrelevant-integer-module-diamond.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Short-complex colimit comparisons: normalize abstract endpoints first

On baseline3b4b58eb with pinned Lean4.34.1, native graphs041–046 failed while
rewriting preservation formulas that mixed `(T ⋙ π₁).obj X` and
`(T.obj X).X₁`. The target could not be checked at implicit transparency.
Local backward-transparency settings and `erw` did not resolve the final
mixed-composite match. Instead prove the preservation square for abstract
functors F,H and a natural transformation α, then instantiate α with the
native short-complex projection transformation using `exact`.

Graph049 accepted `Continuity.ShortComplexColimit` in1.3 seconds with this
repair, without extra transparency options or increased resource budgets.
This is full-leaf native evidence, not a benchmark or a kernel-defect claim.
No additional test, audit or kernel replay was used.

