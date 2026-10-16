# Smooth field schemes and dimension

The native owner is `AlgebraicGeometry.Scheme`. [Properties](Properties.lean) states `SmoothFieldRegularity`, `SmoothFieldNormality`, `SmoothFieldDimension` and `SmoothClosedPointDimension` over every field and in every relative dimension.

| Main result | Exact conditions and conclusion |
| --- | --- |
| `smoothFieldRegularity` | For an arbitrary scheme smooth over a field, every actual stalk is regular local. |
| `smoothFieldNormality` | The same smooth-field hypotheses give domain and integrally closed stalks through the regular-local ring theorems. |
| `smoothOfRelativeDimension_stalk_dimension_le` | Smooth relative dimension `n` gives dimension at most `n` at every stalk. |
| `smoothClosedPointDimension` | Under the same relative-dimension hypothesis, a point with closed singleton has stalk dimension exactly `n`. |
| `smoothFieldDimension` | The scheme dimension is `n` when the smooth relative-dimension-`n` scheme is nonempty. |
| `isReduced_of_smooth_over_field` | Smoothness over an arbitrary field gives reducedness of the actual structure sheaf. |

[Charts](Charts.lean) constructs actual etale polynomial charts under the stated smooth-field hypotheses. The weaker affine etale-chart regularity and dimension results live in [Stalk/EtalePolynomial](../../Stalk/EtalePolynomial.lean); the arbitrary-scheme dimension equality lives in [Stalk/Dimension](../../Stalk/Dimension.lean). Focused imports are `Aglib.AlgebraicGeometry.Morphisms.Smooth.{Charts,Regularity,Normality,Dimension,Reduced}`. [Regular-local algebra](../../../RingTheory/RegularLocalRing/README.md), [polynomial dimension](../../../RingTheory/KrullDimension/README.md) and [actual stalk comparisons](../../Stalk/README.md) supply the lower results.

[Normal component theory](../../Properties/Normal/README.md) keeps local Noetherian/connectedness hypotheses for its own conclusions. [Smooth differential rank](../../Modules/Differentials/README.md) remains a separate explicit input. No fixed dimension-one, curve-property or DVR record is part of this family.
