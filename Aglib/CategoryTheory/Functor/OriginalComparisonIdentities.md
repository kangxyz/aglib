# Whole identity equations on original comparisons

Source: [OriginalComparisonIdentities.lean](OriginalComparisonIdentities.lean).

This small variable-category interface retains the actual functors, original
isomorphisms and actual coefficient arrows. No geometric object occurs.

- `originalComparison_refl_square` proves the entire mapped-reflexivity square
  for three arbitrary functors and an arbitrary compatible coefficient arrow.
- `originalComparison_trans` evaluates an independently proved composition of
  the original isomorphisms using native `Functor.mapIso_trans`.
- `originalComparison_identity_normalization` consumes the original coefficient,
  its comparison, the actual functor-to-identity iso and the proved unnormalized
  equation. It concludes the literal identity arrow, including identity-object
  reduction before specialization.
- `originalDoubleContravariant_id` and `originalDoubleContravariant_map_refl`
  prove complete identity equations for the SAME arbitrary contravariant functor
  applied twice, optionally after another actual functor. They use native
  opposite and functor identity laws; no double-dual functor is constructed.

The geometric consumers supply only their original functors/comparisons and
independently proved laws. These are not desired-law records or substitutes
for constructing geometric maps.

Direct consumers: [AlgebraicGeometry/Modules/Differentials/Relative/ExteriorCoefficientCoherence](../../AlgebraicGeometry/Modules/Differentials/Relative/ExteriorCoefficientCoherence.md).
