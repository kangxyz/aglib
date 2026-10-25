> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#nonflat-base-change-share-the-concrete-coefficient-constructor) · [Context](original-context.md) · [Case index](README.md) · [Previous record](projective-duality-typed-boundaries-before-concrete-geometry.md) · [Next record](formal-line-bundle-algebraization-explicit-transports.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Nonflat base change: share the concrete coefficient constructor

The original-map ring-equivalence transport in
[Map/RingEquiv](../../Aglib/AlgebraicGeometry/Cohomology/BaseChange/Modules/Map/RingEquiv.lean)
first exceeded both 200,000 and 800,000 kernel heartbeats when rewriting the
concrete pullback-unit, composition and equality comparisons together. An
abstract commuting-triangle lemma checked at the standard budget, but its
five-line concrete specialization still exceeded 200,000 heartbeats: a short
application retained an expensive conversion between separately presented
coefficient composites.

The retained source defines `ordinaryPullbackCoefficientMap` once, including
the original unit and native comparison iso. Both the abstract triangle and
the concrete fibre-product coefficient use that same definition head. The
complete leaf then compiled at the standard 200,000-heartbeat policy in
18.2 seconds, with 2.51 GB peak process-group RSS and no guard failure. Both
public Epi and IsIso statements retain the original scalar base-change map
and require no additional flatness, quasicoherence or Noetherian hypothesis.
This establishes a successful proof boundary, not a controlled timing ratio
or a diagnosis of a compiler defect. The general proper-descent consumers
were still pending when this provider measurement was recorded.

The affine sheaf composition in
[Nonflat/AffineSheafComposition](../../Aglib/AlgebraicGeometry/Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineSheafComposition.lean)
exposed the same issue. Abstracting only its final categorical chain, and then
its complete functor calculation, still left the concrete specialization above
the fixed 25,600 MiB process-group limit. The retained
[AffineFunctor](../../Aglib/AlgebraicGeometry/Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineFunctor.lean)
defines one generic arrow constructor used literally in both the abstract
composition statement and the concrete `affineMapOfTilde`. The two native
composition transformations are supplied separately. The generic provider,
affine sheaf provider and composition provider then built in 1.6, 3.0 and
3.0 seconds, respectively, at the standard heartbeat policy; their complete
group peaked at 2.15 GB. The existing shared-iso definition of
`affineMapFromTensor` and its sections formula were retained. This validates
the composition providers; higher-image composition, refinement and global
descent are separate consumers and were still pending at this measurement.

