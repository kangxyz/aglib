# Actual rational domination of a supplied regular model

Source: [RationalDomination.lean](RationalDomination.lean).

Import `Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDomination`.

`Scheme.RationalSingularities.normalModificationH1Vanishing_stalk_over_regular_model`
uses a domain `A` with genuine Nagata property and dimension at most two,
a supplied regular integral proper birational `q : Y -> Spec A`, and an
actual normal integral proper birational comparison `a : T -> Y`.
Every singular original `T`-stalk has universal modification-H1 vanishing.
Noetherianity of `A` follows from Nagata; the original finite-type birational
map `q` supplies both the dimension of `Y` and Nagata of `Y.stalk (a x)`.
The latter is not deduced merely from regularity of that local ring.

`Scheme.NormalizedPointDomination.exists_rational_domination_of_regular_model`
adds normality of `A` and constructs the existing normalized-point domination
output: an actual normalized closed-point chain `beta : T -> Spec A`, its
actual proper birational comparison `a : T -> Y`, the original triangle
`a >> q = beta`, and the original normality, Noetherianity, dimension,
properness and function-field conclusions. It additionally proves universal
H1 vanishing at every singular original terminal stalk.

The generic affine-base domination assembly lives once in
`NormalizedPointDomination.AffineBase`; this regular-model theorem only appends
the original singular-stalk rationality conclusion. Its chart hypotheses use
the original adapted-chart theorem and native global-section isomorphism.
The base need not be local, complete or regular, and no later stalk is
assumed complete or finite over it.

The normal terminal dominates the supplied regular model; terminal
regularity is not concluded. A conditional finite-resolution application
still supplies its initial full cones and earlier complete-base map.
