# Module-linear Ext and actual cohomology

The parent [Ext](../Ext.lean) owns the sole canonical comparison
`moduleExtCohomologyMap`: native exact scalar forgetting on Ext followed by
precomposition with the original constant-integer map representing one.
`moduleExtCohomologyAddEquiv` proves this map bijective for every scheme,
module sheaf and degree. The proof uses actual acyclicity of the additive
sheaves underlying module injectives. Coefficient naturality and Yoneda
composition concern the original maps.

[Scalars](Scalars.lean) equips original structure-module Ext with the action
of global functions by precomposition with `Scheme.Modules.unitMul`.
`moduleExtModuleOfHom` restricts this action along a specified structural
ring map. `moduleExtCohomologyLinearEquiv` is the original canonical
comparison, linear for this source action and the existing coefficient
action on additive cohomology. No scalar action is defined by transport
through a chosen equivalence.

[DegreeZero](DegreeZero.lean) identifies the canonical comparison on H⁰
with `Scheme.Modules.unitHomGlobalSectionsEquiv`. For an original module
morphism this is its value on the actual global section one. The statement
also applies directly to an arbitrary native degree-zero Ext class via
`Ext.addEquiv₀`; no field or quasicoherence premise is needed.

[Linear](Linear.lean) uses the native Mathlib Ext module on the actual
module-sheaf category with `moduleCategoryLinearOfHom X α`. For arbitrary
source and target module sheaves, `moduleExt_smul_precomp_of_hom` and
`moduleExt_smul_postcomp_of_hom` identify this action with original
module-linear scalar multiplication. Native bilinear Yoneda composition,
precomposition, postcomposition and Ext⁰/Hom linear equivalence are
available directly. `moduleExt_native_smul_eq_existing` identifies the
existing unit-source action exactly, and
`moduleExtCohomologyLinearEquivOfCategory` has the same original canonical
Ext/cohomology forward map. The general Ext action allows independent
structural-ring and scheme universes; the cohomology bridge keeps its
existing common universe.

[Restriction](Restriction.lean) constructs
`moduleRestrictionAdditiveComparison` for an arbitrary open immersion.
Its component is literally `moduleCoefficientPullback` of the original
module restriction adjunction unit. On the structure module it becomes the
actual structural pullback map under the original `restrictUnitIso`, and
its integer-one equation retains the original constant-sheaf comparison.
`moduleExtCohomologyMap_restrict` identifies native exact restriction on
module Ext, precomposed with `restrictUnitIso.inv`, with the original
geometric cohomology map for the actual restriction unit in every degree.
No quasicoherence, compactness, Noetherianity or finiteness is required.

[Open](Open.lean) compares actual `Ext(openFree X U, M, n)` with the
unchanged native `Sheaf.H' (moduleAddSheaf X M) n U`. The forward map is
exact native scalar forgetting followed by the actual integer-open
generator representing the module-open universal section. Its degree-zero
formula is the original Hom/section equivalence. Images of module
injectives are flasque on every open, so the sole generic acyclic-injective
comparison proves bijectivity in all degrees. Original module coefficient
maps, Yoneda composition and the restriction maps of `openFreeFunctor`
become the original native open-cohomology maps. The linear equivalence
uses Mathlib's native Ext action from `moduleCategoryLinearOfHom` and the
existing coefficient action on `H'`. `moduleOpenExtCohomologyMap_top`
identifies the top-open comparison with the original structure-module
Ext/`Sheaf.H` comparison through the actual universal morphism representing
one. No quasicoherence, flatness, finiteness or Noetherianity is needed.

[Exact](Exact.lean) identifies the native Ext class of an actual short exact
module-sheaf sequence with the original cohomology connecting map.
`moduleExtCohomologyMap_extClass` and
`moduleExtCohomologyMap_connectingOfHom` retain native Yoneda composition,
the original `moduleCohomologyConnectingOfHom`, and its positive sign.
The inverse additive comparison has the corresponding literal boundary
formula. All schemes, module coefficients, nonnegative degrees and
structural ring maps are allowed; no quasicoherence or finiteness is needed.
The leaf passed `1792102911445337000-34547` and supplies the boundary
normalization for the higher Serre-pairing argument.

[Pullback](Pullback.lean) constructs `modulePullbackAdditiveComparison` as the
original additive inverse-image mate of the native module pullback unit.
Its unit-module and integer-generator equations retain the actual structural
map and native `pullbackUnitIso`, for every scheme morphism.
`moduleExtCohomologyMap_pullback` proves that, for a flat morphism, exact native
module pullback on Ext computes precisely the original geometric cohomology
map with that unit. It applies to every module coefficient and every natural
degree, with the original Ext/cohomology universe; no quasicoherence,
Noetherianity or finiteness is assumed. This comparison supplies the actual
coefficient map used by derived flat base change.

[Invertible](Invertible.lean) gives
`Scheme.Cohomology.lineBundleHomSectionsEquiv` and `lineBundleExtZeroEquivH0`
for an actual line bundle on a field scheme. The equivalence
`Ext⁰(L, M) ≃ₗ[K] H⁰(M tensor L.dual)` uses the original structural field
scalar action. Its lower tensor equivalence works on arbitrary schemes in
[DualTensorEquivalence](../../../Modules/Invertible/DualTensorEquivalence.lean).
