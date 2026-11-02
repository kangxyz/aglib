# Actual completed intermediate-field branches

Import `Aglib.AlgebraicGeometry.Surfaces.Resolution.CompletedIntermediateBranch`.
The namespace is `AlgebraicGeometry.Scheme.IntermediateFieldModel`.

Use the original complete Noetherian local domain `R` of dimension at most
two, finite faithful normal domain `A/R`, native fraction fields `F` and `K`,
and literal intermediate field `L`. The geometric input is only a supplied
proper birational integral model `a : Y -> Spec (integralClosure R L)` of
the intermediate ring. Every construction is the existing normalized Cover,
its original finite projection `pi` and original proper birational map `b`.
There is no supplied resolution of `A` or replacement model.

`finiteChart_nagata_and_dimension` uses the actual finite inverse-image
affine chart of `pi`. Nagata ascent, integral incomparability and original
stalk localization prove `sourceStalk_nagata_and_dimension` and
`source_dimension_le_two` before any closed-point or branch selection.
`singular_point_closed_dimension` then proves that every actual singular
source point is closed and has a dimension-two original stalk.

For `dim A = 2`, `singular_completion_normalDomain` proves that this literal
stalk's maximal-adic completion is both a domain and integrally closed.
The proof derives locality and completeness of original `A` from its finite
original coefficient algebra. The native proper closed-image argument puts
the original point over the closed point of `A`. The original structural
scalar map is local and injective; the proved original residue square
transports actual finite-type closed-point residue finiteness. The existing
normal-surface completion theorem applies directly to that original stalk.
No later stalk is assumed finite over `A`, complete, or already normal after
completion. This original map argument is implemented once by
`Scheme.Hom.normalDomain_completion_stalk_of_complete_surface` in
`Stalk.CompleteSurface`; this consumer derives its own complete-base, closedness,
dimension and Nagata inputs and delegates to that same proof.

For an actual full-algebra branch `q`, `singular_branch_target_dimension`
proves the original target stalk is two-dimensional, through the original
branch localization and the **whole** finite algebra. If the supplied
intermediate model is regular, `singular_branch_completed_properties` gives
a regular two-dimensional completed target, a normal two-dimensional completed
source, and finiteness/injectivity of the accepted canonical completed map.
Their actual fraction degree is at most `[K:L]` and strictly below `[K:F]`
when `F < L`. The independent `intermediate_induction_degree_lt` proves
`[L:F] < [K:F]` from `L < K`; no numerical decrease is a premise.

`singular_branch_completed_compatibility` retains the same canonical maps at
every finite quotient, their original coefficient equation, and both original
function-field and residue squares. `exists_singular_completed_branch`
supplies an actual maximal branch for each original singular point and
its strictly smaller actual completed degree.

This establishes the geometric and completed-degree data needed by later
strong induction. It does not invoke induction, construct a finite normalized
closed-point chain, or prove final resolution existence or regular-locus
isomorphism. Supplied-resolution-to-chain conversion remains a separate
obligation.
