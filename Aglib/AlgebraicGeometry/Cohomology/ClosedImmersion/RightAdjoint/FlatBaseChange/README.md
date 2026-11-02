# Original quotient charts and flat-base-change sources

[QuotientChart](QuotientChart.lean) constructs mapped-ideal quotient charts
from an actual affine Cartesian square. The source map is the native
pullback lift and its ideal is literally the original ideal mapped by
the structural ring homomorphism. Both projection equations are retained.
[ChartUniqueness](ChartUniqueness.lean) proves equality of the full ideals
and source maps for two charts over the same affine ambient map, using
the original quotient maps and the required monomorphism.

[ChartRefinement](ChartRefinement.lean),
[AffineOpenRefinementRings](AffineOpenRefinementRings.lean) and
[LiteralQuotient](LiteralQuotient.lean) retain the original mapped ideals
under open refinement and prove the literal quotient squares Cartesian.
Flatness is a separate hypothesis where used; ring commutativity alone
does not supply it.

[SourcePresentation](SourcePresentation.lean) compares the original
localized quotient presentation with the mapped-ideal quotient through
its native ring equivalence and unit laws. Its Ext/counit equations use
the same resolution and retain quasicoherence and the selected Ext world.
[ProjectiveCover](ProjectiveCover.lean) constructs these charts on the
original projective field-extension pullback over common-universe fields,
without requiring a finite coordinate index. These structural interfaces
do not themselves assert arbitrary canonical sheaf gluing.

Present consumers include [AffineOpenRefinementRings](AffineOpenRefinementRings.md), [ChartRefinement](ChartRefinement.md).
