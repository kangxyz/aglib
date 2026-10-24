# Shared constructions and equations

Return to the [performance lookup](../PERFORMANCE.md).
Use this topic when an abstract proof succeeds but its concrete application
still expands costly structures, or when a small proof has an expensive type
comparison. First identify the [conversion boundary](conversion-boundaries.md).

## Share one regular equation in producer and consumer

State the original equation through a regular definition with the actual
objects and arrows as arguments, and use that same head in the generic proof,
concrete statement and consuming proof. Recorded examples include `CompEq`,
`GlobalSectionImagesEq`, `QuotientFinite`, `CompletionImageEq` and
`ExactComparisonSquareEquation`.

The concrete witness remains proved from the original construction; the
definition does not supply a new mathematical premise. Wrapping only one side,
or separately specializing all the intermediate calculations, was insufficient
in several [conormal](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#preserve-regular-equations-through-conormal-comparisons)
and [completed-stalk](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#keep-the-completed-stalk-equation-through-specialization)
comparisons.

In the gluing examples, `CompEq f g h` was used on both sides, with compatible
arguments inside `mapComp'`. One-sided wrapping gave no gain. Two other `rw`/`simp`
proofs barely improved. The proposed reduction-order explanation
was not established by a kernel trace.
[Original equation and structure-field observations](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#equation-proofs-presentations-and-structure-fields).

## Share the actual constructor

When two large data chains are independently reconstructed, a theorem about
them may not remove conversion at specialization. Use one actual regular
function, functor or comparison head in the definitions and statements. If
needed, construct the relevant data inside the generic producer.

A tensor-chart repair required constructing the tensor comparison inside the
shared chart witness; merely sharing its original arrow witness had still
failed. Coefficient-single repairs similarly delivered tests at the actual
`zmodSingle` head expected by the provider.
[Tensor witness](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#construct-the-tensor-comparison-inside-the-shared-chart-witness),
[coefficient-single cases](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#share-the-actual-coefficient-single-data-head-before-transporting-exchange-tests).

A witness can keep an arrow and its original value/projection equations
together. Project that same witness rather than rebuilding its value and proof
independently. The original maps and the equations they satisfy must remain
the interface.

More packaging is not automatically faster. Motivic's first history context
changed the recorded constructor time from 135 seconds to 300; two packaging
variants took 294 and 319. Moving the complete supplier conversion into the
abstract producer led to 141 seconds, which does not improve on 135.
[Local case, table and limits](https://github.com/kangxyz/motivic/blob/main/docs/performance/local-cases.md#history-context-and-complete-supplier-conversion).

Another recorded boundary proved additive-group algebra over variable
`[AddCommGroup A]` before specializing it to `PicardGroup`. The repaired full
module was later reported at 244 seconds, but baseline sources were not retained
and the runs were unmatched. The proposed explanation that concrete Picard
structure was unfolding remains a candidate, not measured declaration attribution.
[Picard tangent-space report](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#picard-tangent-space-prove-additive-group-algebra-abstractly-then-specialize).

## Name repeated equation proofs consistently

Use the same named degree or transport lemma, with atomic arguments, when it is
needed in both a statement and its proof. This applies to dependent transports
inside `eqToHom`, `pullbackCongr` and `mapComp'`.

In the Koszul case, independently presented proofs of degree equations triggered
costly conversions. A restated variable-degree lemma was reported at 114 seconds
and 25 GB, while the named-degree version took 2 milliseconds; the repaired
Koszul leaf was reported at 6.4 seconds and 2.5 GB.
[Original conditions and measurements](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#equation-proofs-presentations-and-structure-fields).

Proof irrelevance still requires compatible proof types. The record's proposed
proof-type/delta explanation is a candidate explanation for those observations,
not a general attribution of kernel cost.

## Preserve the reduction interface

Check that the actual consumer can still use the required component equations.
A local constructor over abstract functors may retain a literal component through
beta/zeta reduction; a separately applied proof helper can introduce conversion
between new instance proofs.

The Godement Span observations include such a rejected helper and a retained
local constructor. Producer savings elsewhere also moved work into callers.
[Span and Tensor evidence](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#what-the-measurements-establish),
[cost transfer](build-and-check-costs.md#producer-and-consumer-cost).

A public name need not expose its body. True Lean `opaque` changes reduction
behavior; abstract theorem parameters in these records are not a recommendation
to replace canonical definitions with `opaque`. Expose the needed equations
through the actual interface rather than changing transparency globally.

## Compare an isomorphism with its value before projecting

For an identified conversion between a regular isomorphism definition and its
value, prove a named `rfl` value equation at variable arguments. Transport it
through `congrArg`, then compose with the existing lemma before specializing
the heavy geometry.

In `HilbertScheme/DirectImageSheafQuotient.lean`, the `Iso`-level value equation
and the value-side instance each checked below 0.1 seconds, while a
definition-side instance took 45 seconds. Plain application of generic lemmas
and tensor-presentation alignment did not resolve it. The repaired full module
was reported at 24 seconds with profiling and 18 seconds without.
[Retained observations and failed alternatives](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#hilbert-scheme-direct-images-compare-isomorphism-values-at-the-iso-level).

Projection/delta order remains a proposed mechanism in that record. This case
supports the targeted value bridge, not a general replacement for `rw` or
`exact`.
