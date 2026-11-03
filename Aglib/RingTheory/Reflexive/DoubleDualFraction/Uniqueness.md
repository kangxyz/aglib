# Original evaluation determines bidual maps into torsion-free targets

Source: [Uniqueness.lean](Uniqueness.lean).

Let `f : M -> V` be the specified localization at the nonzero divisors
of `R`, with `M` finitely presented and `V` reflexive over the original
fraction field `K`. The original `doubleDualToFraction f` is injective
and sends original evaluation to `f`.

`exists_nonZeroDivisor_smul_eq_eval` proves once that every actual bidual
element has a nonzero-divisor multiple equal to an original evaluation.
It uses localization surjectivity and the original generic embedding.
`doubleDual_linearMap_ext_on_eval_of_torsionFree` then proves equality of
maps into any torsion-free target by cancelling that regular scalar.
This is a uniqueness theorem, not an assertion that raw evaluation is epi.
No reflexivity or torsion-freeness of the raw module is assumed.

The existing generic-fibre theorem retains its original statement and
maps. It is a wrapper: original localization units give torsion-freeness
of `V`, then the general target theorem applies. The existing uniqueness
of `doubleDualToFraction` remains unchanged.

The geometric consumer uses the original affine bidual section/evaluation
comparison and invertible target-line sections to prove compatibility
of the same global one-pole map with its original local maps. No desired
compatibility, canonical trace comparison or sheaf map is assumed.

Direct consumers: [RingTheory/Kaehler/PureDegreePTrace/Localization](../../Kaehler/PureDegreePTrace/Localization.md).
