# Original linear affine chart restriction

Source: [AffineChartRestrictionMap.lean](AffineChartRestrictionMap.lean).

The native affineChartRestrictionLinearMap is the original restriction unit,
original affine pushforward global-sections comparison, and original chart
restriction isomorphism. Its whole function, actual presheaf restriction,
unit-coordinate law, principal specialization, and actual-affine-open
specialization are proved here under their original hypotheses.

These are the generic definitions formerly private in IntegralTrace's held
AffineFormsLocalization owner. They are moved once into the native module
namespace; no parallel implementation remains in that owner. Their bodies
are unchanged apart from consistent names. No quasicoherence, finite type,
normality, nonempty-open or localization premise is added.

Direct consumers: [AlgebraicGeometry/Modules/Differentials/Relative/ExteriorAffineRestriction](../Differentials/Relative/ExteriorAffineRestriction.md), [AlgebraicGeometry/Modules/InternalHom/AffineOpenDualLocalization](../InternalHom/AffineOpenDualLocalization.md), [AlgebraicGeometry/Modules/Locality/AffineChartPullback](AffineChartPullback.md).
