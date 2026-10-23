# Quasicoherent structure-module sheaves

The objects are actual `X.Modules` with Mathlib's quasicoherence property. [Affine](Affine/README.md) compares them with native modules through tilde/global sections. [FiniteType](FiniteType/README.md) adds actual finite generators, while [Localization](Localization/README.md) supplies denominator and quasi-compact-open direct-image arguments.

[Limits](Limits.lean) in `AlgebraicGeometry.Scheme.Modules.QuasiCoherent` detects quasicoherence on every actual affine chart and gives the actual kernel/limit closure through affine exactness. [Pullback](Pullback.lean) transports actual quasicoherent presentation data through the geometric pullback. [FlatPullback](FlatPullback.lean) compares affine pullback with actual extension of scalars and gives the stated monomorphism/short-exact preservation under flatness of the scheme map.

Focused imports follow these three leaves and the subfamilies. Quasicoherence and finite type require no locally Noetherian premise merely to define the objects. [Coherent](../Coherent/README.md) is the later locally Noetherian abelian/exact specialization; module-resolution affine cohomology and canonical base change consume the lower quasicoherent results.

[Homology](Homology.lean), imported as `Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Homology`, proves `quasicoherent_of_openNeighborhoods`: a module sheaf is quasicoherent if every point has an actual open neighborhood on which its restriction is quasicoherent. `quasicoherent_homology` proves that `K.homology i` is quasicoherent for every integer `i` when every term `K.X n` is quasicoherent. Both statements hold on arbitrary schemes; the homology result requires neither a term bound nor local Noetherianity. The [perfect-complex homology results](../PerfectComplexes/Homology.lean) combine these statements with the separate [ordinary-complex homology comparisons](../Complex/Homology.lean).

[Tensor](Tensor.lean), imported as
`Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor`, identifies the actual
sheaf tensor of two native tilde modules with tilde of their module tensor.
`tildeTensorIso_hom_tmul` preserves the original sheafification-unit formula on
every open. `isQuasicoherent_moduleTensorLeftFunctor` proves tensor closure on
arbitrary schemes without flatness, finiteness, or Noetherian hypotheses; the
module owner has no cohomology dependency.

[AffinePushforward](AffinePushforward.lean) proves quasicoherent direct image
for an arbitrary affine morphism, not just a map between affine schemes.
It uses restriction to actual affine charts and the original open-base-change
comparison. No Noetherian hypothesis is required.

[Coproduct](Coproduct.lean) proves arbitrary small colimit closure, in
particular quasicoherence of the actual ambient module-sheaf coproduct.
[Affine/CoproductSections](Affine/CoproductSections.lean) proves that original
affine-open section cocones remain colimiting for quasicoherent diagrams.
Both statements preserve the actual cocone maps and require no finite-type,
Noetherian, flatness or separatedness premise.

[ShortExact](ShortExact.lean) proves `Scheme.Modules.isQuasicoherent_X₁_of_shortExact`: the first term of a short exact sequence of module sheaves is quasi-coherent when the other two are, through `QuasiCoherent.quasicoherent_kernel`.
