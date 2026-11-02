# Rationality of singular original stalks over a regular target

Source: [RegularTarget.lean](RegularTarget.lean).

Import `Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.RegularTarget`.
The namespace is `AlgebraicGeometry.Scheme.RationalSingularities`.

`normalModificationH1Vanishing_stalk_of_regular_target` takes an ORIGINAL
proper dominant birational map `a : T -> Y` of integral schemes, normal `T`,
regular locally Noetherian `Y` with stalk dimensions at most two, and an
actual singular point `x : T`. It also requires Nagata of the ORIGINAL
local ring `Y.stalk (a x)`; regularity alone does not discharge that premise.
Its conclusion is universal normal-modification H1 vanishing at `T.stalk x`.

The original isomorphism locus excludes `a x`, so the actual target local
ring has dimension exactly two. The proof uses the LITERAL pullback along
`Y.fromSpecStalk (a x)`, derives integrality and normality, and proves that
its structural map is birational through the original pullback square and
original function-field maps. Nagata of the target local ring bounds that
actual model's dimension. Its lifted singular point is therefore closed
and nongeneric. Neither global closedness of `x` nor a dimension bound or
Noetherianity of the entire `T` is an extra premise.

Regular-local vanishing and the existing local rationality-propagation
theorem apply on this model. The right component of the SAME original
stalk-arrow isomorphism and the RingEquiv theorem transport the result to
the original `T.stalk x`; no replacement cohomology or residue maps are used.

A complete-local degree-induction consumer must derive the explicit Nagata premise from
its actual finite-type birational model over a genuine Nagata base. This
leaf does not assume the selected source stalk finite over an earlier
base or complete. It proves neither Gorensteinness, completion rationality,
terminal regularity, a resolving chain, nor final resolution existence.

The original local-spectrum field square and cancellation now have one
lower owner, FunctionField/LocalSpectrum/BaseChange. This consumer retains
its exact public telescope and delegates only that existing body.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/RationalDomination](../Resolution/RationalDomination.md).
