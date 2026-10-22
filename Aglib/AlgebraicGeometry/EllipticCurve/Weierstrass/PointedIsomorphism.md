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
The public `affineAlgEquiv_exists_variableChange_with_coordinates` retains
that same chosen change together with both original x/y recovery equations.
The earlier `affineAlgEquiv_exists_variableChange` is its thin coefficient-only
consequence; all existing public statements and simp registrations are
preserved. The classification calculation occurs once. The separate
`PointedVariableChange` consumer uses the retained equations to identify the
original projective isomorphism, rather than only its coefficient orbit.

This minimal interface refactor starts from the selectively adopted published
source `c4e27ffface9d767f8d3348c823da299789a80945c4fde8dac4dd17715166586`
at publication `a4313d00c58e453c45603724e9a7fbf9050afd44`. Its Spec.map coercion
and explicit canonical arguments are preserved. The adopted source and guide
are archived separately. The changed Lean source
`5dd444494002ad4762cf88c280cd28ff66acd0f0e9c949d27c23127d75bafab0`
passed its native leaf in 9.9 seconds in
`remote-e88eb7d69a10450791de9b57fb693946`, SOURCE
`01ba21339e8262b1d7da0963b031afbbcc781decf650917e5e2a65855651d8b2`.
Other leaves failed independently in that shared graph. This source remains
unchanged; the separate `PointedVariableChange` leaf also has its own native
pass for the full original-map equality. These leaf results do not replace
independent mathematical review.
