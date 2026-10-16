# Ordinary complexes of scheme module sheaves

The object is the actual integer-indexed `CochainComplex X.Modules ℤ`. A complex here has no term bound unless a statement explicitly supplies `K.IsStrictlyGE a`; bounded-below and derived objects have their own interfaces.

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.Complex.Basic`, constructs `Scheme.Modules.Complex.restrict` for an actual open immersion and `pullback` for an arbitrary morphism. Restriction preserves finite limits, finite colimits, homology and actual quasi-isomorphisms. Pullback is additive; its finite-limit, homology and quasi-isomorphism preservation retain `Flat f`. `pullbackRestrictIso` compares actual pullback with restriction to an inverse-image open. This leaf also gives `Scheme.Modules.restrictModule_isFlasque` for an actual flasque module sheaf restricted along an open immersion. `Scheme.Modules.Complex.restrict_isStrictlyGE` transports a supplied strict lower term bound. `ordinaryOpenRestrictionIso` and its `ordinaryOpenRestrictionIso_hom_f` equation identify the actual component maps of ordinary direct image and open restriction, for an arbitrary morphism and the displayed target open.

[Tensor](Tensor.lean) supplies `Scheme.Modules.Complex.tensorLeft`, `tensorRight` and `tensorLeftRightIso` on actual cochain complexes. `tensorLeftRestrictionIso` and `tensorRightRestrictionIso` compare them with actual open restriction, for arbitrary coefficient sheaves. Additivity needs no finite-local-freeness hypothesis; finite-limit/finite-colimit preservation and `tensorRight_quasiIso` retain finite local freeness of the coefficient. The tensor-order and restriction equations use the canonical sheaf tensor.

[AcyclicSupport](AcyclicSupport.lean) gives `Scheme.Modules.Complex.pullback_acyclic` and `pullback_restrict_acyclic` under flatness of the actual morphism. Tensor acyclicity on either side requires finite local freeness of the coefficient and acyclicity of the original complex. `coprod_acyclic` and `coprod_restrict_acyclic` require both complexes to be acyclic on the indicated scope. Support here means acyclicity after restriction to the exact displayed open; the pullback statement uses its actual inverse-image open.

Lower inputs are the actual module functors, [stalk detection](../Stalk/README.md), [locally free tensor exactness](../LocallyFree/Tensor/README.md) and generic homological algebra. Godement comparisons and derived open-cover detection consume these ordinary maps. No compactness, quasicoherence or perfect-complex predicate is imposed by the general complex interfaces.

[Homology](Homology.lean) gives `homologyIsoOfDerivedIso` through the native
derived homology factorization and `restrictHomologyIso` through the actual
exact restriction comparison. The original homology sheaves are retained.
The derived category has the standard morphism universe `u + 1` for
`X : Scheme.{u}`. These results precede [local perfect models](../Perfect/README.md).

[Sections](Sections.lean) detects actual `ExactAt` and acyclicity in any
complex shape from original variable-ring sections on a topological basis.
Its `quasiIso_of_sections_on_basis` detects actual quasi-isomorphisms of
integer cochain complexes by those native section maps. It imports no
cohomology implementation and assumes no quasicoherence, termwise
acyclicity, boundedness or finiteness. The proof uses exact conservative
native scalar forgetting and the established additive-sheaf basis criterion.
The leaf passed `1792103250738244000-40548`; the independent raw-evaluation
and arbitrary-index-universe consumer passed `1792103303811904000-41257`,
with only the three standard axioms.

[Tilde](Tilde.lean) applies the original affine `fromTildeΓNatTrans` counit
to actual module complexes of any shape. `tildeGlobalSectionsCounit_f`
and `tildeGlobalSectionsCounit_toOpen` retain the literal original counit
and its section-localization unit equation. The chain map is natural in
original coefficient chain maps. When this actual counit is a
quasi-isomorphism, `tildeGlobalSectionsHomologyIso` computes the original
homology sheaf from the native affine section-complex homology, using the
exact tilde comparison and the homology map of that same counit. The
resulting original homology sheaf is quasicoherent.

The same leaf identifies native module localization with actual tilde
sections on `D(r)` through the original `tilde.toOpen`. This section functor
is exact, and its original complex unit localizes actual homology in every
shape and degree. `tildeBasicOpenComplexUnit_counit` is the exact chain-map
equation saying that this unit followed by the original counit equals the
original top-to-open restriction. Consequently,
`tildeGlobalSectionsCounit_quasiIso_of_isLocalized` proves the actual
integer-cochain counit a quasi-isomorphism when those actual homology
restrictions localize on every principal open. It uses the native section
basis criterion, with no assumption of quasicoherence of the target terms
or homology.

[Tilde/HomologyMap](Tilde/HomologyMap.lean) identifies the actual affine counit
with the native complex-adjunction counit. The original complex mate followed
by this counit recovers its specified sheaf-complex arrow.
`tildeGlobalSectionsHomologyIso_mate` computes that arrow on homology using
only exact tilde and the stated quasi-isomorphism of the actual counit.
Its `_mate_sections_unit` and `_mate_sections` equations retain the original
tilde units and native homology isomorphisms in affine section coordinates.
They hold in every complex shape and independent index universe, without a
hypothesis that global sections preserve homology. The proved direct-image
counit supplier and canonical derived base-change normalization are consumers.
