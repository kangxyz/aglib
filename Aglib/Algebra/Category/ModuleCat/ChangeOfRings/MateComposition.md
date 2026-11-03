# Whole mates of scalar-extension composites

Source: [MateComposition.lean](MateComposition.lean).

`homEquiv_extendScalarsComp_map_comp` evaluates the existing complete scalar
adjunction comparison on the original morphism composite, not on tensor
values. It retains arbitrary commutative rings and modules in universe u,
original raw maps f/g, t:extend_f P→Q and s:extend_g Q→N.

The proof calls existing `homEquiv_extendScalarsComp`, then uses scalar unit
naturality and restrictScalarsComp.inv naturality to expose the pre/postcomposed
whole-morphism result. It neither reproves the scalar conjugation backend nor
cancels a unit. Its only import is Mathlib's native ChangeOfRings owner.
The native affine presented-map mate theorem is its current consumer.
