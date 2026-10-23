# Original quotient conormal compatibility

Import `Aglib.AlgebraicGeometry.ProjectiveBundle.RankTwoExtension.Conormal.Compatibility`.
The namespace is `AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension`.

`frameRestrictionIso` uses the native composition and equality comparisons
on the original affine frame inclusions. `frameHomCompatible_of_refinement`
uses affine frames refining each range intersection to pass from whole-arrow
refinement squares to `InternalHom.RestrictionHomCompatible` on the actual
pullback overlaps. `quotientConormalFramesCompatible_of_refine` applies this
to the actual `quotientConormalRestrictionIso` family. Its premise
`QuotientConormalFramesRefine` states the exact intermediate refinement equation.

`Conormal.infinityConormal_translation` compares the actual conormal action
of the original unipotent projective-line automorphism with the identity.
It uses the same principal overlap, actual coordinate maps and canonical
conormal maps as `Conormal.overlapConormalMaps_equal`.
`Conormal.coordinateConormal_coefficient` retains the original coordinate
frame under arbitrary coefficient ring homomorphisms. The underlying
`conormalSquareMap` is the canonical map of the actual pulled-back kernel
ideals from `IdealSheaf.Modules.ConormalMap`.
`Conormal.chart_coefficient` identifies the original polynomial chart maps
with the literal projective coefficient map. `Conormal.infinityConormal_coefficient`
and `Conormal.infinityConormal_transition` then give naturality of the actual
infinity frame under coefficient changes and the original unipotent transition.


`Conormal.FrameMapCompatible` and `Conormal.PullbackFrameRefinement` are
regular proposition definitions of the same canonical arrow equations.
Generic transport proofs and their concrete chart applications use these
same propositions, so the equations retain explicit module objects across
the specialization. They add no hypothesis to the final compatibility theorem.

The construction transports these local frames through the original
source-spectrum isomorphisms, pastes the original quotient-section chart
squares, and identifies the pullback comparison with the native restriction
comparison. `quotientConormalFramesCompatible` and `quotientConormalIso`
have only the original short exact extension hypotheses.
`quotientConormalIso_hom_restrict` specifies every original local frame.

The complete module passed native compilation with default budgets in run
`remote-123316c95d424e5d98b249b27da5de4a`. The compiled Lean source has SHA-256
`edf1223ad5f5c00cc93161fbcb59fd92ecf9c4eee6c6e96e7cdd72567f98fc42`.
This closes the global conormal compatibility sub-obligation under the
original short exact extension premises, including the canonical isomorphism
and preservation of every original local frame. The V1 H¹-injection,
Grauert–Riemenschneider vanishing and surface capstone remain separate obligations.
