# Scalar extension of Kähler and exterior differentials

[BaseChange](BaseChange.lean) defines
`CommRingCat.KaehlerDifferential.affineDifferentialLinearMap` for composable
maps `Λ → A → B` of commutative rings in the same universe.
It is the native differential base-change map in `ModuleCat` and sends
`b ⊗ d a` to `b • d(σ a)`.

[ExteriorBaseChange](ExteriorBaseChange.lean) gives the scalar-extension
map in every exterior degree with the original wedge and scalar action.
[ExteriorCoordinate](ExteriorCoordinate.lean) uses a supplied `Fin n` basis
of the differential module to identify its top exterior power with the
coefficient ring: `r` maps to `r` times the ordered basis wedge.
This coordinate needs no domain hypothesis.
The affine sheaf and relative-form comparisons consume these maps.

Present consumers include [Relative differentials over arbitrary scheme bases](../../../../AlgebraicGeometry/Modules/Differentials/Relative/README.md).
