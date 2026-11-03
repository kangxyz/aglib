# The actual complete intermediate integral closure

Source: [CompleteIntermediateField.lean](CompleteIntermediateField.lean).

Import `Aglib.RingTheory.IntegralClosure.CompleteIntermediateField`.
The namespace is `integralClosure`.

Start with a finite faithful algebra of domains `R -> A`. Use the native
`FractionRing R` and `FractionRing A`, with the existing
`FractionRing.liftAlgebra R (FractionRing A)` action of the original map.
For an actual `IntermediateField` L of that extension, the ring in this file
is literally `integralClosure R L`, denoted B below.

`completeIntermediate_fieldFinite` derives finiteness of the original field
extension. `completeIntermediate_fractionRing` identifies the actual L as B's
fraction field; `completeIntermediate_normal` proves normality of B. The
coefficient map's injectivity and unit reflection are proved, not supplied.

`intermediateAmbientMap` is exactly the composite of the native inclusions
`B -> L -> FractionRing A`. Its local algebra action is pinned so that installing
the later B-action on A does not silently change the original ambient action.
It is not a replacement field or a different fraction-field embedding.

When A is normal, `intermediateToOriginal` is the native
`IsIntegralClosure.lift R A (FractionRing A)`. Its `fraction` equation says that
its image in the original upper fraction field equals the original intermediate
inclusion. That equation proves injectivity and the original fraction scalar
tower. The B-action on A comes from this same map. Finiteness follows by
restricting the original finite R-module structure, and the map reflects units.
If R and A have dimension two, the actual integral contractions give
`dim A <= dim B <= dim R`, hence dimension two of B.

If R is a complete Noetherian local domain of dimension at most two,
`completeIntermediate_finite` derives finiteness of B from current CN2.
The subsequent declarations prove B Noetherian and local, then prove its
**own maximal-adic completeness**. The completeness proof uses finite-module
completeness for the extended original maximal ideal and the existing proved
`finiteLocalAlgEquiv`, whose coefficient equation identifies the actual map
into the maximal completion. No cofinal exponent is assumed.

This lower assembly does not need R to be regular, A to be complete or local,
a proper intermediate-field hypothesis, or a resolution. For complete-local degree induction, the original
finite regular subring provides its hypotheses. The geometric consumer must
use a supplied resolution of this actual B and the existing normalized Cover;
this file supplies neither a resolution of A nor a completed-branch degree
or chain-termination oracle.

The maximal-adic completeness statement uses the generic lower theorem
`IsAdicComplete.maximalIdeal_of_finite_local` after installing the already
proved original finite algebra, local ring and local coefficient map.
The ideal-comparison proof has one implementation in `FiniteLocalComplete`;
the intermediate-closure interface and its original maps are unchanged.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/IntermediateFieldModel](../../AlgebraicGeometry/Surfaces/Resolution/IntermediateFieldModel.md).
