# Regularity of the original Cartier section on the coefficient canonical module

Source: [RegularCanonicalSection.lean](RegularCanonicalSection.lean).

## Statements

`cmCurveCoefficientCanonical_cartierTensorSection_mono` retains the original
projective embedding, coefficient module `V` of dimension one, ambient dimension
index and its coordinate equivalence, and the closed-stalk CM parameter condition.
For an actual closed immersion `i : D → C` with its original ideal locally free
of rank one and `D` finite over the original ground field, it proves monicity of
`(cartierTensorSection i).app W`, where `W` is the own-homology coefficient
canonical module. The field is arbitrary and the curve need not be reduced.

`cmCurveCoefficientCanonical_cartierCoefficientSequence` proves short exactness
of the original positive Cartier coefficient row and actual finite closed
support of its literal pushforward/pullback quotient. It does not replace the
section, quotient unit, extension class, or coefficient line by chosen models.

`pullback_cartierTensorSection_eq_zero` identifies literal geometric pullback
of the same section with zero, using the original quotient-unit equation under
the original adjunction. This retains the actual closed zero scheme.

## Proof route

Naturality and exact tensoring by the dual ideal show that the original Cartier
section vanishes on its own kernel. Tensor compatibility, braiding naturality,
and the original evaluation identity imply that the original ideal inclusion
acts as zero on this kernel. Evaluation on native pure-section tensors proves
annihilation by the original kernel ideal sheaf.

An arbitrary module annihilated by a closed ideal with finite field-valued zero
scheme has finite closed support: the zero scheme is compact and locally
Artinian, hence finite discrete; its actual points are enumerated, mapped by the
original closed immersion, and the original ideal-action stalk lemma gives
vanishing elsewhere. The same argument applies to every original pushforward,
without a quasicoherence assumption.

The canonical kernel is quasicoherent and a finite-type subobject of the actual
coherent canonical module. The previously proved coefficient purity theorem
kills it. The existing Cartier row theorem then gives short exactness, with
its original maps unchanged.

The last elaboration issue was isolated by native stage markers and then by
binding the support theorem without an expected type. This exposed ambiguous
`pullback` (geometric module pullback versus the categorical fiber product).
The final proof qualifies the original module functor and normalizes only the
original row projection and functor composition. This follows the existing
PERFORMANCE guidance on original typed boundaries and colliding names; no
new performance rule or unverified speedup claim is needed.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/AnticanonicalHilbert](../AnticanonicalHilbert.md).
