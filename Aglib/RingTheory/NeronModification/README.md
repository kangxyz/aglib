# Affine Néron modifications

[`Basic`](Basic.lean) constructs the actual quotient imposing `p * Zᵢ = gᵢ`, then quotients
by the kernel of localization away from `p`. The resulting image of `p` is
regular. A map to a ring where the image of `p` is regular, together with
specified divisibility witnesses, factors uniquely through this construction
and preserves the original coefficients and the specified coordinates.
The index type is arbitrary and the original `p` need not be regular.

[`Lift`](Lift.lean) expresses this universal property as an algebra
homomorphism. Its uniqueness theorem retains regularity of the image of `p`
in the target.

[`BaseChange`](BaseChange.lean) constructs an algebra equivalence between a
flat scalar extension of the modification and the modification of the extended
coefficients. It preserves the original coefficients and the specified divided
coordinates. Flatness supplies the regularity used to construct the inverse.

[`ChangeGenerators`](ChangeGenerators.lean) gives a comparison map from an
inclusion of the centre ideals `span ({p} ∪ range g)`, and an algebra equivalence
when these ideals are equal. The original coefficient map is preserved.

[`Localization`](Localization.lean) proves that localizing the coefficient
ring localizes the actual modification at the images of the old scalars.
The algebra structure is induced by the constructed comparison map.

These are affine algebraic transformations. The Néron desingularization
invariant, its strict decrease, smoothness of an eventual stage, and Artin
approximation are not asserted by this family.
