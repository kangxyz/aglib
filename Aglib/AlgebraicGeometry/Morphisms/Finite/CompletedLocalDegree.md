# Degree of the original completed stalk map

Source: [CompletedLocalDegree.lean](CompletedLocalDegree.lean).

Import `Aglib.AlgebraicGeometry.Morphisms.Finite.CompletedLocalDegree`.
The namespace is `AlgebraicGeometry.Scheme.Hom.LocalNormAlgebra`.

Retain the finite dominant map of integral schemes, original nonempty affine
chart and original target point of `CompletedLocalModel`. For an actual maximal
ideal `q` of the existing **whole** finite local algebra `Ring f U hU y`, set
`R = O_Y,y` and `T = O_X,branchPoint(q)`. Both completions below are their own
maximal-adic completions; neither carrier is replaced.

`completedStalkMapAt` transports the existing `FiniteSemilocal.baseAlgebra`
map through the completion of the same original stalk equivalence.
`completedStalkMapAt_eval` identifies every finite quotient with the literal
quotient map of `stalkMapAt`. `completedStalkMapAt_unique` proves that these
same-precision equations uniquely determine the completed map. Agreement only
on original, uncompleted elements is not used as a uniqueness argument.

The assumptions are deliberately split:

- A **Noetherian target stalk** supplies source-stalk Noetherianity by
  localization of the whole finite algebra, then `completedStalk_finite` and
  `completedStalkMapAt_isLocalHom`. No finite selected-stalk or global
  Noetherian-scheme premise is introduced.
- A **regular target stalk** supplies domainhood of its completion and
  `completedStalkMapAt_injective`, using the existing torsion-free completed
  branch embedding. Source-completion domainhood is unnecessary for this step.
- **Domainhood of the actual source-stalk completion** is used only for its
  fraction field. `completedFractionMapAt` is the universal lift of the proved
  injective completed map. Its algebra-map equation retains the original
  coefficient inclusion. `completedFraction_finite` proves finiteness, and
  `completedFraction_finrank_le` bounds the degree by the degree of the original
  `Scheme.functionFieldMap f`.

The degree proof transports `FiniteSemilocal.exists_branch_embedding` to the
literal source completion and applies the native fraction-rank equality. It
does not reconstruct the semilocal product, count factors, choose another
function field, or accept a smaller-degree assertion.

`completedStalkMapAt_residue_square` retains the original residue maps through
the native completion residue maps. `completedFraction_original_field_square`
uses the actual generic-stalk map and universal lifts of the native local
completion maps. These are equations of original maps, not just field
isomorphism or numerical equalities.

`exists_completedStalkMap_degree` obtains an actual branch for every original
closed source point over the selected target point. Its canonical completed
map, injectivity, finiteness, lifted fraction map, and degree bound are on that
literal source-stalk completion.

This is not a surface-resolution existence theorem. For complete-local degree induction the target-stalk
regularity must come from the supplied regular model of the actual intermediate
integral closure. Normality and domainhood of the source completion must be
proved from the complete original surface base, original local and residue
maps, Nagata property, and dimension. The later surface consumer must identify
the original generic degree with `[K:L]` through the actual birational square
and prove strict decrease from the proper intermediate field. Those geometric
discharges and the noncircular conversion of a supplied resolution to a finite
normalized point chain are not premises silently supplied by this leaf.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/CompletedIntermediateBranch](../../Surfaces/Resolution/CompletedIntermediateBranch.md).
