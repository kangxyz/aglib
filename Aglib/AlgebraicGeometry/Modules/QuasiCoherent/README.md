# Quasicoherent structure-module sheaves

The objects are actual `X.Modules` with Mathlib's quasicoherence property. [Affine](Affine/README.md) compares them with native modules through tilde/global sections. [FiniteType](FiniteType/README.md) adds actual finite generators, while [Localization](Localization/README.md) supplies denominator and quasi-compact-open direct-image arguments.

[Limits](Limits.lean) in `AlgebraicGeometry.Scheme.Modules.QuasiCoherent` detects quasicoherence on every actual affine chart and gives the actual kernel/limit closure through affine exactness. [Pullback](Pullback.lean) transports actual quasicoherent presentation data through the geometric pullback. [FlatPullback](FlatPullback.lean) compares affine pullback with actual extension of scalars and gives the stated monomorphism/short-exact preservation under flatness of the scheme map.

Focused imports follow these three leaves and the subfamilies. Quasicoherence and finite type require no locally Noetherian premise merely to define the objects. [Coherent](../Coherent/README.md) is the later locally Noetherian abelian/exact specialization; module-resolution affine cohomology and canonical base change consume the lower quasicoherent results.
