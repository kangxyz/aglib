# Commutative rings and finite-stage models

[Localization](Localization.lean), imported as `Aglib.Algebra.Category.Ring.Localization`, supplies `CommRingCat.localizationAway_map_comm` and `CommRingCat.ker_localizationAway_map` for arbitrary commutative-ring maps and chosen principal localizations.

The statements use the actual `algebraMap` and `IsLocalization.Away.map`. Their commutative square and literal kernel equation require no scheme, smoothness, flatness or surjectivity assumption. [Spectral localization](../../../AlgebraicGeometry/Spec/Localization.lean) consumes these lower ring equations.

[Descent.FinitePresentation.Models](Descent/FinitePresentation/Models.md) constructs an
actual finitely presented algebra at a stage of a filtered commutative-ring
colimit, with its specified tensor algebra equivalence to the original
algebra. Finite coefficient and relation data are placed at a common stage;
the ring maps need not be injective or flat. The scheme and module descent
families use this lower producer.
