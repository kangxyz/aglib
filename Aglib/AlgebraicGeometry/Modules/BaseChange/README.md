# The canonical pullback/direct-image mate

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.BaseChange.Basic`, constructs `AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap f g M`. For the actual fibre square, its source is `g* f_* M` and target is the direct image of the pulled-back module. It is the mate of the original counit, with the actual pullback-composition comparisons.

`structureModuleBaseChangeMap` specializes it to the actual unit module. `pullbackStructureUnitIso` identifies the pulled-back structure module with the source unit. `fieldSections` and `moduleFibre` give actual field-valued section/fibre modules and scalar-preserving map/isomorphism interfaces.

[Affine](Affine.lean), imported as `Aglib.AlgebraicGeometry.Modules.BaseChange.Affine`, proves `moduleBaseChangeMap_isIso`: for affine `f`, arbitrary quasicoherent coefficients and arbitrary `g`, the constructed map is invertible. `affineModuleBaseChange : AffineModuleBaseChange` supplies the complete existing theorem family without an additional mathematical premise. No flatness, Noetherianity or finite-generation hypothesis is used. The retained `structureModuleBaseChangeMap_isIso` interface takes the family as `hbase`; pass `affineModuleBaseChange` to obtain its structure-module specialization.

[Affine/Mate](Affine/Mate.lean) identifies `moduleBaseChangeMap` with the native `cartesianBaseChangeMap` on its actual fibre square. `pullbackSquareIso` is the original composition/equality comparison, and `conjugateEquiv_pullbackSquareIso` identifies its conjugate with the original pushforward square. `cartesianBaseChangeMap_eq_counit` and `moduleBaseChangeMap_unit` retain the original geometric counits and units. These normalization results apply to arbitrary schemes and module sheaves, without quasicoherence or affineness assumptions.

[Scalar base change](../../../Algebra/Category/ModuleCat/ChangeOfRings/BaseChange.lean) supplies `ModuleCat.scalarBaseChangeMap`, the original scalar-adjunction mate for a commuting square `R → S`, `R → T`, `S → P`, `T → P`. Its source is `T ⊗[R] M`, with `M` first restricted from `S`, and its target is `P ⊗[S] M`, restricted to `T`. The original units give the literal formula `1 ⊗ m ↦ 1 ⊗ m`. `scalarBaseChangeMap_isIso_of_isPushout` identifies this map with the inverse native `Algebra.IsPushout.cancelBaseChange` equivalence and proves invertibility for every module and commutative-ring pushout. No flatness, Noetherianity or finite-generation hypothesis is used.

[Affine/Sections](Affine/Sections.lean) proves `specBaseChangeSectionsMap_eq_scalarBaseChangeMap`: the actual geometric mate on a commutative-ring pushout becomes this scalar mate through the native pullback/sections and pushforward/sections comparisons. `cartesianBaseChangeMap_isIso_spec` therefore proves invertibility of the actual cartesian map for every spectrum pushout and arbitrary quasicoherent coefficients. `affinePullbackGlobalSectionsIso_one_tmul` retains the original geometric unit, and `isIso_of_globalSections_isIso` reflects isomorphisms between actual affine quasicoherent sheaves.

[Affine/GlobalSections](Affine/GlobalSections.lean) transports the same native tilde/global-section adjunction through each affine scheme's canonical `isoSpec`. `affineΓFunctor`, `affineTildeFunctor` and `affineTildeAdjunction` are the displayed composites of the original functors. The original unit is invertible, and the original counit is invertible for arbitrary quasicoherent coefficients. `affinePushforwardGlobalSectionsIso` compares actual direct image with restriction along `f.appTop` for any morphism between affine schemes; its forward and inverse maps are identity on actual top sections. These comparisons also prove quasicoherent direct-image preservation between arbitrary affine schemes and reflection of isomorphisms on actual affine sections.

[Affine/PullbackSections](Affine/PullbackSections.lean) gives `affinePullbackSectionsIso` for arbitrary affine schemes and quasicoherent coefficients. Its `_unit` and `_one_tmul` equations retain the original geometric adjunction unit. [Affine/AllAffine](Affine/AllAffine.lean) proves `affineBaseChangeSectionsMap_eq_scalarBaseChangeMap` on the actual global-section-ring pushout and then `cartesianBaseChangeMap_isIso_of_isAffine` for the original mate on every cartesian square of affine schemes. The final affine-morphism theorem descends this result over affine source and target opens using the actual open and composition comparisons; it keeps arbitrary base schemes and arbitrary changes of base.

[Composition](Composition.lean) proves `cartesianBaseChangeMap_comp` on two supplied successive cartesian squares. It identifies the original iterated mates through the original pullback-composition isomorphisms, for arbitrary module sheaves. There is no quasicoherence, flatness or affine premise in this compatibility equation.

[OpenImmersion](OpenImmersion.lean) supplies the canonical `openBaseChange` isomorphism from actual restriction adjunction and pullback square. [Field fibres/rank](../LocallyFree/README.md), coherent pushforward and [relative evaluation/cohomology](../../Cohomology/BaseChange/README.md) consume these exact maps. Schemes and coefficient fields keep universe `u` in the fibre interface.

[Cartesian](Cartesian.lean) constructs the actual comparison on a supplied cartesian square. [Coefficients](../../BaseChange/Coefficients/README.md) packages arbitrary over-scheme/algebra coefficient pullbacks and polynomial/Laurent naturality; [OpenImmersion](OpenImmersion/README.md) gives the actual generic open-base-change comparison and section formulas without quasicoherence or coherence. General cartesian comparison-map construction does not assert unconditional invertibility.

[Affine](Affine/README.md) supplies the existing `AffineModuleBaseChange` family for affine `f`, quasicoherent coefficients and arbitrary base change. The literal canonical `moduleBaseChangeMap` and original mate/restriction equations are preserved; no flatness of the change-of-base morphism is assumed.

[OpenImmersion/Pullback](OpenImmersion/Pullback.lean) proves that the existing restriction-adjunction isomorphism is exactly `cartesianBaseChangeMap` after the native `restrictFunctorIsoPullback` comparisons. `isIso_cartesianBaseChangeMap_of_isOpenImmersion` supplies invertibility of the original pullback mate for open base change and arbitrary module sheaves, without quasicoherence.

The open comparison's adjunction-unit equation is named
`restrictFunctorIsoPullback_inv_adjunction_unit`. The existing
`restrictFunctorIsoPullback_inv_unit` in `Modules/Restriction/Unit` concerns
the monoidal unit object. Both keep their actual maps and distinct meanings.

[Adjoint](Adjoint.lean) proves `cartesianBaseChangeMap_adjoint` for an actual
cartesian square and arbitrary module sheaves. It identifies base change of
the original adjoint, followed by the actual `cartesianBaseChangeMap`, with
the adjoint of the original pulled-back arrow. This is an equation of the
specified maps, with no invertibility, quasicoherence, flatness, or Noetherian
premise. The
[formal/algebraic adjunction comparison](../../Cohomology/GrothendieckExistence/FormalAlgebraicAdjunction.lean)
uses it to retain the original modification adjoint under completion.

[Counit](Counit.lean) proves `pullback_counit_eq_of_isPullback`: on a cartesian square the pullback
of the counit `f^* f_* M ⟶ M` is the base-changed counit after `cartesianBaseChangeMap` and the
square comparison; `epi_pullback_counit_of_isPullback` transfers epimorphy when the mate is
invertible. Arbitrary module sheaves.

[FreeMap](FreeMap.lean) defines the adjoint `pushforwardFreeMap π ψ : free I ⟶ π_* M` of a map out
of a free sheaf, with its basis sections (`ιFree_pushforwardFreeMap`,
`unitHomGlobalSectionsEquiv_ιFree_pushforwardFreeMap`), composition on the right
(`pushforwardFreeMap_comp_right`), the vanishing criterion `comp_pushforwardFreeMap_eq_zero_iff`,
the free comparison along a commutative
square (`pullbackFreeIso_square`) and base change along a cartesian square
(`pushforwardFreeMap_baseChange`), for arbitrary module sheaves. The pullback counterpart
`pullbackFreeMap` is [Pullback/FreeMap](../Pullback/FreeMap.lean).

[CartesianInvertibility](CartesianInvertibility.lean) proves
`isIso_cartesianBaseChangeMap_of_isIso_moduleBaseChangeMap`: the mate of every cartesian square is
invertible when `moduleBaseChangeMap` of the chosen pullback is, through `IsPullback.isoPullback`,
`cartesianBaseChangeMap_comp` and the open-immersion case.

[Congr](Congr.lean): the cartesian base-change map of two equal squares, compared through
`pullbackCongr` (`cartesianBaseChangeMap_congr`).
