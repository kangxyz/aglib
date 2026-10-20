# Smooth morphisms, geometric regularity and dimension

[GeometricRegularity](GeometricRegularity.lean) proves
`smooth_iff_flat_and_geometricallyRegular` for locally finitely presented
morphisms over an arbitrary base. For a locally Noetherian target,
`smooth_iff_locallyOfFiniteType_and_flat_and_geometricallyRegular` characterizes
smoothness by local finite type, flatness and geometrically regular fibers.
No affine, quasi-compact or fixed-dimension hypothesis is imposed.

[Field](GeometricRegularity/Field.lean) proves smoothness from geometric
regularity for any locally finite-type scheme over any field. Its converse
uses `smoothFieldRegularity` after base change. The algebraic supplier is
[the arbitrary-field regularity criterion](../../../RingTheory/Smooth/GeometricRegularity.lean).
The geometric predicate records actual stalk regularity after every field
base change; the stated finiteness hypotheses ensure those schemes are locally
Noetherian. Flatness remains explicit in the relative equivalences.

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

[Normal component theory](../../Properties/Normal/README.md) keeps the stated component, local Noetherian and connectedness hypotheses for its own conclusions. [Smooth differential rank](../../Modules/Differentials/README.md) is supplied separately by `Scheme.Modules.Differentials.differentialSheaf_hasRank_of_smooth`; its [relative counterpart](../../Modules/Differentials/Relative/README.md) proves rank `n` for every smooth morphism of fixed relative dimension `n` over an arbitrary base. Neither theorem requires a supplied rank family. No fixed dimension-one, curve-property or DVR record is part of this family.

[RegularScheme](RegularScheme.lean) proves
`Smooth.of_regularStalks_of_perfectField` for the actual structural map to a
perfect field: local finite type, local Noetherianity of the original scheme
and `Scheme.RegularStalks` are the stated hypotheses. This is a regular-to-smooth
supplier; it does not assert the remaining curve-construction inputs.

[StandardEtaleChart](StandardEtaleChart.lean) supplies `Scheme.StandardSmoothEtaleChart.coordinateMap` from the native standard-smooth theorem. The chart is exactly `Spec.map` of that chosen ring map, with its original algebra-map compatibility triangle. Over a regular base ring, `regularStalks` uses the native actual-stalk etale theorem and `Scheme.regularStalks_spec`; the relative dimension, algebra structures and common universe remain explicit.
