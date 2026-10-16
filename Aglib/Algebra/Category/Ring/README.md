# Canonical localization maps in CommRingCat

[Localization](Localization.lean), imported as `Aglib.Algebra.Category.Ring.Localization`, supplies `CommRingCat.localizationAway_map_comm` and `CommRingCat.ker_localizationAway_map` for arbitrary commutative-ring maps and chosen principal localizations.

The statements use the actual `algebraMap` and `IsLocalization.Away.map`. Their commutative square and literal kernel equation require no scheme, smoothness, flatness or surjectivity assumption. [Spectral localization](../../../AlgebraicGeometry/Spec/Localization.lean) consumes these lower ring equations.
