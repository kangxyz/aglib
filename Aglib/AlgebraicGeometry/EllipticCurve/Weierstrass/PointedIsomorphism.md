# Pointed isomorphisms and the j-invariant

[PointedIsomorphism.lean](PointedIsomorphism.lean) supplies
`pointedWeierstrassJInvariant : PointedWeierstrassJInvariant` with the original
all-fields statement, nonzero discriminants, and literal projective cubics
and origins.

An actual pointed projective isomorphism restricts to the two actual affine
complements. The base-field algebra equivalence is the pullback of its inverse
restriction; its Spec identity is explicit. The principal-ideal colength
argument in [PoleBasis.lean](PoleBasis.lean) forces triangular coordinate
images. Comparing the cubic coefficient gives `b² = a³`, and `u = b/a`
provides the admissible scale over the same field. The remaining coefficient
comparison identifies the target with the native variable-change action, so
Mathlib's invariant formulas give the required equality of `c₄³/Δ`.

The coordinate classification is a proved conclusion of an actual algebra
isomorphism. It is not an input to the pointed-isomorphism theorem.
