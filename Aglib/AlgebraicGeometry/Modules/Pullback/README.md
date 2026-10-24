# Canonical module pullback comparisons

[Isomorphism](Isomorphism.lean) proves that actual module-sheaf pullback
along a scheme isomorphism is an equivalence. Its inverse is the original
pullback along the inverse morphism, with native composition, congruence
and identity comparisons.

[Free](Free.lean) constructs actual pullback comparisons for the structure module, free sheaves and open restriction. The unit/free generator index sets are retained; the maps come from the native pullback adjunction.

[FreeComp](FreeComp.lean) proves that `pullbackFreeIso` respects Mathlib's composition, identity and equality comparisons of pullbacks (`pullbackFreeIso_comp`, `pullbackFreeIso_id`, `pullbackFreeIso_congr`); the first two are checked on the summand inclusions through `pullbackUnitIso_comp` and `_id`. Its consumer is the quotient functor of [Grassmannian/Quotient](../../Grassmannian/README.md).

[FlatMorphism](FlatMorphism.lean), imported as `Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism`, gives `Scheme.Modules.pullbackModuleStalkIso` with extension of scalars along the actual stalk map. `flatExactPullback` and `shortExact_pullback_of_flat_all` retain flatness of the scheme morphism for exactness on arbitrary coefficients.

[OpenRestriction](OpenRestriction.lean) owns the actual scheme restriction/pullback-square helpers below the invertible tier. The arbitrary-site `PresheafOfModules.Restriction` constructions and `PresheafOfModules.isIso_of_locallyBijective` are imported from [module-presheaf sheafification restriction](../../../Algebra/Category/ModuleCat/Presheaf/SheafificationRestriction.lean). The scheme criterion `Scheme.Modules.locallyBijective_of_local_isIso` consumes the same original local maps.

Consumers are finite-presentation/quasicoherent transport, [arbitrary vector-bundle pullback](../LocallyFree/README.md), invertible tensor pullback and cohomological base change. Exactness for all module sheaves under a flat morphism and exactness for locally split vector-bundle sequences under arbitrary morphisms are separate results.

[Unit](Unit.lean), [StalkUnit](StalkUnit.lean) and [SectionStalk](SectionStalk.lean) fix the original pullback unit and its actual section/germ and stalk scalar-extension formulas. They are lower maps used by canonical projection and base-change comparisons, not additional curve/coherent interfaces.

[TensorAdjunction](TensorAdjunction.lean) and [LocalBases](LocalBases.lean)
compare the actual pullback/tensor adjunction and transported local bases.
Their maps are the original pullback maps, with the displayed scheme and
module hypotheses.

[LocalSpectrum](LocalSpectrum.lean) normalizes the actual stalk map of
`fromSpecStalk` and identifies the original module stalk with global sections
of its actual local-spectrum pullback. The factors are the native scalar
extension unit, original pullback-stalk comparison, and inverse closed germ;
no quasicoherence or finiteness hypothesis is required.

[UnitTriangle](UnitTriangle.lean) retains the original pullback units and native
composition/equality comparisons on a commutative scheme triangle.

[Triangle](Triangle.lean) holds `pullbackTriangleIso a b d h : pullback b ⋙ pullback a ≅ pullback d` for a commutative triangle (`pullbackComp`, then `pullbackCongr`), its associativity `pullbackTriangleIso_assoc_hom` from `pullbackComp_assoc_hom`, the component, unit, free-sheaf and three-triangle identities, and `overPullback E T = (T ⟶ S)^* E` with `overPullbackIso`. Consumers: [Descent/FinitePresentation/Modules/Maps](../../Descent/FinitePresentation/Modules/Maps.lean) and [Grassmannian/LocallyFree](../../Grassmannian/README.md).

[FreeTransfer](FreeTransfer.lean) transfers a map `ιK : K ⟶ 𝒪_T^I` along `π : X ⟶ T` and
`p : X ⟶ P` to `freeTransfer π p ιK : π^* K ⟶ p^* 𝒪_P^I` and proves its base change along a
commutative square through the comparison `pullbackSquareIso` of
[BaseChange/Affine/Mate](../BaseChange/Affine/Mate.lean) (`pullbackSquareIso_hom_freeTransfer`),
for arbitrary morphisms and modules.

[FreeMap](FreeMap.lean) defines the pullback `pullbackFreeMap q m : free I ⟶ q^* F` of a map out of
a free sheaf, with its composition, congruence and basis-inclusion laws (`pullbackFreeMap_comp`,
`pullbackFreeMap_congr`, `pullbackFreeMap_comp_right`, `ιFree_comp_pullbackFreeIso_inv`), for
arbitrary `q`. The direct-image counterpart is [BaseChange/FreeMap](../BaseChange/FreeMap.lean).

[UnitSections](UnitSections.lean) computes the global section of a pulled-back section map
through the adjunction unit (`pullbackUnitIso_inv_one`,
`unitHomGlobalSectionsEquiv_pullbackUnitIso_inv_comp`). The second is a public restatement of the
private `unitHomGlobalSectionsEquiv_pullback` of
[ResolutionSections/Pullback](../../Cohomology/DirectImage/ResolutionSections/Pullback.lean).
