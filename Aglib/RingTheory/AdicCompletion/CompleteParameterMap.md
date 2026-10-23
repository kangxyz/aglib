# Completion of the original parameter map

Let f:B→A be a ring map between local rings, with A Noetherian and
complete for its actual maximal ideal. Assume the extension of
maximalIdeal B has radical maximalIdeal A. The construction
`AdicCompletion.localParameterMap f h` is an actual ring map from
AdicCompletion (maximalIdeal B) B into A.

Write J=maximalIdeal(B).map f. Finite generation of maximalIdeal A
gives a positive N with (maximalIdeal A)^N⊆J⊆maximalIdeal A.
The map is the composite of the literal `AdicCompletion.idealMap`,
the cofinal-power `sandwichAlgEquiv`, and the inverse of A's original
maximal-adic completion map. Its original-element equation is

```text
localParameterMap f h (algebraMap B (AdicCompletion (maximalIdeal B) B) b) = f b.
```

When B is Noetherian, the completion's maximal ideal is the extension
of maximalIdeal B. The original-element equation therefore gives the
exact extended-ideal equality with J, and hence locality of the map.

If the original residue composite B→A→ResidueField A is surjective,
the actual completed scalar map onto the same residue field is also
surjective. Thus that field is a finite module over the completed
source. The actual quotient A/J maps onto it with finitely generated
nilpotent kernel. Native
`Module.finite_of_surjective_of_ker_le_nilradical` proves A/J finite
over the completed source. The original module quotient is identified
with A/J using `Ideal.smul_top_eq_map` and the native restriction-of-scalars
quotient equivalence. The passed adic coefficient-lifting theorem now
proves A itself finite over the completed source. No finiteness premise
on A as a source module is used.

If B is regular local and A has the same finite dimension as B, the
actual completed map is injective. The completion remains regular and
preserves dimension, so it is a domain. A nonzero element of its kernel
would give an integral map from the quotient by that nonzerodivisor
into A. Integral incomparability makes contraction on prime spectra
strictly monotone, bounding dim(A) by the quotient dimension. The native
nonzerodivisor dimension inequality then contradicts equality of the
two finite dimensions.

The hypotheses concern the original local map, its parameter ideal and
residue point. Finiteness and injectivity of the completed map are derived
from them. Constructing a suitable polynomial source is a separate use of
this interface.

Source basis: Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The mathematical inputs are the native ideal/quotient maps, proved completion comparisons,
nilpotent-kernel finiteness, adic coefficient lifting, integral
incomparability, and the native nonzerodivisor dimension drop.
