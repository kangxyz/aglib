# Ambient regularity along a regular Cartier closed subscheme

[RegularQuotient.lean](RegularQuotient.lean) proves regularity of the actual
ambient stalks along a closed immersion `i : Z ⟶ X` whose actual ideal module
`Scheme.Hom.idealModule i` is locally rank one.

- `Hom.ker_stalkIdeal_eq_ker_stalkMap i z` identifies
  `i.ker.stalkIdeal (i z)` with `RingHom.ker (i.stalkMap z).hom`.
- `Hom.isRegularLocalRing_stalk_image_of_isLocallyRankOne_ideal i hI z`
  assumes only Noetherianness of the ambient stalk at `i z` and regular
  locality of the source stalk at `z`.
- `Hom.isRegularLocalRing_stalk_image_of_cartier i hI hZ z` specializes this
  to a locally Noetherian ambient scheme and `RegularStalks Z`.

Local rank one is pulled back along the canonical `X.fromSpecStalk (i z)`.
The existing triviality theorem for line bundles on a local spectrum and the
canonical local-spectrum sections/stalk comparison identify the original
ideal-module stalk with the ambient local ring. The existing
`Hom.idealModuleStalkEquiv` identifies that same stalk with the original stalk
ideal. The displayed kernel equality then yields a rank-one free presentation
of the actual stalk-map kernel.

The closed immersion supplies surjectivity of this actual stalk map. The
[ring adapter](../../../RingTheory/RegularLocalRing/RankOneKernel.lean) uses its
canonical quotient equivalence and the existing regular-principal-quotient
theorem to conclude regularity of the ambient stalk. No ambient regularity,
normality, integrality, coefficient field, separability or excellence is
assumed. The result only concerns points in the closed image; propagation to
the whole ambient scheme is a separate obligation.

Source basis: Aglib `22f7532679eec4295167fcf885cf8b1b0981d899`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. The current consumer
is the general surface contraction construction. Native compilation is
coordinated by the root task.
