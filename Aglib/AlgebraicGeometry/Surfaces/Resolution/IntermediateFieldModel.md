# The actual normalized cover of an intermediate-field model

Import `Aglib.AlgebraicGeometry.Surfaces.Resolution.IntermediateFieldModel`.
Declarations live in `AlgebraicGeometry.Scheme.IntermediateFieldModel`.

The coefficient data are the same finite faithful algebra of domains `R -> A`
and actual intermediate field `L` of the native extension
`FractionRing R -> FractionRing A`. The latter action is the original
`FractionRing.liftAlgebra`. The ring B is literally `integralClosure R L`.
A is normal, so `baseMap` is the spectrum map of the canonical lower-leaf
`intermediateToOriginal R A L`. Its finiteness and dominance are derived.

`originalFieldEquiv` and `intermediateFieldEquiv` are the native fraction-ring
identifications, not independent choices. `baseMap_field_square` is proved on
original B-elements using the actual Spec generic-stalk square and the lower
lift's fraction equation. It determines the whole original field map.
`baseMap_field_finite` and `baseMap_field_finrank` then derive finiteness and
exact degree `[FractionRing A : L]` for that original map.

Supply an integral scheme Y and a dominant morphism `a : Y -> Spec B` whose
**original** function-field map is an isomorphism. A genuine regular proper
birational B-resolution from induction supplies this data. The construction
uses literally the existing `NormalizedBlowupCover.Cover.normalization`,
`pi`, `b`, `eta`, `genericLift` and `toPullback`; there is no new model structure.
Regularity is not an unused premise of this construction. It remains available
from the induction input for the later completed-branch consumer.

The original Cover has normal stalks without a separability assumption.
`pi_field_finrank` identifies the original pi degree with the same actual
intermediate degree by the original a/b field maps and `Cover.square`.
`pullbackNormalizationIso` identifies that same Cover with normalization of
its literal original generic lift to `pullback a baseMap`. The comparison
preserves both the original generic arrow and the existing `toPullback` map.
It selects no replacement component or replacement function field.

If R is a complete Noetherian local domain of dimension at most two and a is
proper, actual nonempty affine Y-charts are Nagata and have dimension at most
two. The proof uses finite Nagata ascent for B, the native Gamma-Spec isomorphism
and the original adapted affine chart map in GF2. Thus `pi_isFinite` derives
finiteness of the same normalization without a chart-Nagata premise.
`normalization_isLocallyNoetherian` and `b_proper_birational` concern that same
model and original map back to Spec A. `Cover.square` and `Cover.eta_b` remain
the original square and generic triangle.

No exact dimension-two premise, R-regularity premise or A-completeness premise
is needed just for this construction. The lower leaf supplies B's dimension two
from the original exact dimensions when needed downstream. This file does not
prove completed-source-domain discharge, strict completed-degree decrease,
regularity of the normalized Cover, a finite normalized closed-point chain,
or the final resolution criterion. In particular, no resolution of A is input.
