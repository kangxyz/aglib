# The Hilbert functor and the Hilbert scheme of projective space

This family formalizes the Hilbert functor `Hilb^Φ` of `P^n_A = ProjectiveSpace A ι`, its
embedding into a Grassmannian and, for a Noetherian ring `A`, its representability on locally
Noetherian test schemes by a locally closed subscheme of the Grassmannian, following Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1: §1, pp. 2–4 (the functor), §5,
pp. 24–27 ("Use of m-Regularity", "Embedding Quot into Grassmannian", "Use of Flattening
Stratification", property (F); the proof of Theorem 5.2 for `E = 𝒪`). Throughout,
`A` is a ring, `ι ≃ Fin (n + 1)` (or `[Finite ι]` where stated), `Φ : ℚ[X]` and
`m = hilbertRegularityBound n Φ`. Closed subschemes are Mathlib's `Scheme.IdealSheafData`, with
structure module `quotientModule` ([IdealSheaf/QuotientModule](../IdealSheaf/QuotientModule.lean)).

| Leaf | Main declarations | Hypotheses |
| --- | --- | --- |
| [Functor](Functor.lean) | `subschemeHilbertPolynomial`, `IsHilbertFamily`, `IsHilbertFamily.comap`, `hilbertFunctor` | any `T` over `Spec A` |
| [Regularity](Regularity.lean) | `projectiveHilbertFunction_unit`, `hilbertRegularityBound`, `add_two_le_hilbertRegularityBound`, `isProjectiveRegular_idealModule`, `IsHilbertFamily.isProjectiveRegular_fiber` | field `k`, `e : ι ≃ Fin (n + 1)` |
| [DirectImage](DirectImage.lean) | `idealModulePullbackIso`, `relativeFlat_idealTwist`, `subsingleton_moduleCohomology_idealTwist`, `projective_moduleCohomology_idealTwist`, `isIso_moduleCohomologyBaseChangeMap_idealTwist`, `moduleFiberCohomologyDimension_idealTwist`, `epi_globalSectionsEval_idealTwist` | `B` Noetherian, `Z` flat over `B` with fiber polynomials `Φ`, `r ≥ m` |
| [QuotientDirectImage](QuotientDirectImage.lean) | `quotientTwistFiberIso`, `subsingleton_moduleCohomology_quotientTwist`, `projective_moduleCohomology_quotientTwist`, `isIso_moduleCohomologyBaseChangeMap_quotientTwist`, `moduleFiberCohomologyDimension_quotientTwist`, `exact_moduleCohomology_twistedShortComplex` | as above |
| [Injectivity](Injectivity.lean) | `idealTwistSections`, `le_of_idealTwistSections_subset`, `eq_of_idealTwistSections_eq` | as above |
| [Affine](Affine.lean) | `IsHilbertFamily.flat_comap_pointMap`, `IsHilbertFamily.primeFiber_comap_pointMap`, the direct images of `I_{Z_x}(r)`, `IsHilbertFamily.eq_of_idealTwistSections_eq` | `x : Spec B ⟶ T`, `B` Noetherian |
| [GrassmannianPoint](GrassmannianPoint.lean) | `rankAtStalk_moduleCohomology_quotientTwist`, `rankAtStalk_moduleCohomology_idealTwist`, `grassmannianPoint`, `mem_idealTwistSections_iff`, `eq_of_grassmannianPoint_eq` | `B` Noetherian, `r : ℕ`, `r ≥ m` |
| [ResidueField](ResidueField.lean) | `subschemeHilbertPolynomial_comap_map`, `isHilbertFamily_iff_residueField` | `[Finite ι]` |
| [Point](Point.lean) | `IsHilbertFamily.grassmannianPoint`, `IsHilbertFamily.projective_moduleCohomology_quotientTwist`, `IsHilbertFamily.eq_of_grassmannianPoint_eq` | `x : Spec B ⟶ T`, `B` Noetherian |
| [FlatteningBridge](FlatteningBridge.lean) | `fiberHilbertPolynomialAt_quotientModule_eq`, `IsHilbertFamily.fiberHilbertPolynomialAt_quotientModule_eq`, `isHilbertFamily_iff_fiberHilbertPolynomialAt`, `isHilbertFamily_iff_relativeFlat_and_fiberHilbertPolynomialAt` | `[Finite ι]` |
| [FlatteningStratum](FlatteningStratum.lean) | `fiberHilbertPolynomialAt_congr`, `isHilbertFamily_comap_pullbackBaseChange_iff`, `exists_lift_flatteningStratumι_iff_isHilbertFamily` | the last: `S`, `T` locally Noetherian |
| [GrassmannianFunctor](GrassmannianFunctor.lean) | `unitTwistH0Equiv`, `IsHilbertFamily.grassmannianFunctorPoint`, `IsHilbertFamily.eq_of_grassmannianFunctorPoint_eq` | `B` Noetherian `A`-algebra |
| [Naturality](Naturality.lean) | `restrictionH0_unitTwistH0Equiv_rTensor_eq_zero`, `map_ofLinearEquiv_grassmannianPoint`, `IsHilbertFamily.map_grassmannianFunctorPoint`, `noetherianAffineGrassmannianNatTrans`, `noetherianAffineGrassmannianNatTrans_app_injective` | `B`, `B'` Noetherian |
| [GrassmannianTransport](GrassmannianTransport.lean) | `natCard_degree_eq_choose`, `noetherianAffineGrassmannianNatTransFin` | `e : ι ≃ Fin (n + 1)` |
| [FieldCohomology](FieldCohomology.lean) | `projectiveCohomologyDim_quotientTwist_zero_cast`, `projectiveCohomologyDim_idealTwist_zero_cast`, `projectiveCohomologyDim_idealTwist_zero`, `subsingleton_moduleCohomology_quotientTwist_of_field` | field `k`, `e : ι ≃ Fin (n + 1)`, `r ≥ m` |
| [DirectImageSheaf](DirectImageSheaf.lean) | `familyQuotientTwist`, `directImageSheaf`, `familyQuotientTwistPointIso`, `IsHilbertFamily.fibreCohomologyConcentrated`, `IsHilbertFamily.sheafHasRank_directImageSheaf`, `IsHilbertFamily.isIso_moduleBaseChangeMap_directImageSheaf` | `T` locally Noetherian, natural `r ≥ m` (the fibres: any `T`) |
| [DirectImageSheafQuotient](DirectImageSheafQuotient.lean) | `familyMonomialMap`, `directImageQuotientMap`, `directImageQuotientMap_baseChange`, `isIso_cartesianBaseChangeMap_baseChangeMap_of_isOpenImmersion`, `IsHilbertFamily.isIso_cartesianBaseChangeMap_baseChangeMap` | any `T` (the last: locally Noetherian, `r ≥ m`) |
| [DirectImageSheafEpi](DirectImageSheafEpi.lean) | `epi_pushforward_twistedRestriction`, `IsHilbertFamily.epi_directImageQuotientMap` | `T` locally Noetherian, natural `r ≥ m` |
| [LocallyNoetherianPoint](LocallyNoetherianPoint.lean) | `IsHilbertFamily.grassmannianQuotient`, `IsHilbertFamily.grassmannianMap`, `IsHilbertFamily.grassmannianMap_comp` | `T`, `T'` locally Noetherian, natural `r ≥ m` |
| [LocallyNoetherianFunctor](LocallyNoetherianFunctor.lean) | `locallyNoetherianHilbertFunctor`, `locallyNoetherianGrassmannianFunctor`, `locallyNoetherianGrassmannianNatTrans` | `e : ι ≃ Fin (n + 1)`, natural `r ≥ m` |
| [UniversalSubscheme](UniversalSubscheme.lean) | `homogeneousEvaluationPairing`, `twistedEvaluationMap`, `evaluationIdeal`, `evaluationIdeal_eq_of_iso`, `evaluationIdeal_comap_baseChangeMap` | any `T` over `Spec A`; base change: `K` quasi-coherent |
| [UniversalSubschemeGrassmannian](UniversalSubschemeGrassmannian.lean) | `evaluationIdeal_kernel_comap_baseChangeMap`, `universalEvaluationIdeal`, `universalEvaluationIdeal_comap`, `universalEvaluationIdeal_comap_classifyingMap`, `universalHilbertSubscheme`, `universalHilbertSubscheme_comap_classifyingMap` | `e : ι ≃ Fin (n + 1)`, `N = (n + r).choose r` |
| [IdealTwist/Family](IdealTwist/Family.lean) | `familyIdealTwist`, `familyTwistedShortComplex`, `pointMapIdealPullbackIso`, `pointMapIdealTwistIso` | `Z` flat over `T` for the isomorphisms |
| [IdealTwist/Fiber](IdealTwist/Fiber.lean) | `IsHilbertFamily.fibreCohomologyConcentrated_familyIdealTwist` | any `T`, natural `r ≥ m` |
| [IdealTwist/DirectImage](IdealTwist/DirectImage.lean) | `IsHilbertFamily.relativeFlat_idealModule`, `IsHilbertFamily.relativeFlat_familyIdealTwist`, `IsHilbertFamily.sheafHasRank_pushforward_familyIdealTwist`, `IsHilbertFamily.isIso_moduleBaseChangeMap_familyIdealTwist`, `isLimitPushforwardFamilyTwistedKernelFork`, `epi_of_isKernel_pushforward_familyTwistedShortComplex` | flatness: any `T`; rank and base change: `T` locally Noetherian, natural `r ≥ m` |
| [IdealTwist/BaseChange](IdealTwist/BaseChange.lean) | `baseChangeMapIdealTwistIso`, `IsHilbertFamily.pushforwardFamilyIdealTwistBaseChangeIso` | as above, `f : T' ⟶ T` over `Spec A` |
| [IdealTwist/GlobalGeneration](IdealTwist/GlobalGeneration.lean) | `IsHilbertFamily.epi_counit_familyIdealTwist`, `IsHilbertFamily.imageIdealData_tensor_counit` | `T` locally Noetherian, `r ≥ m` |
| [IdealTwist/Untwist](IdealTwist/Untwist.lean) | `familyTwistPairingIso`, `familyIdealUntwistIso`, `familyIdealTwistLift`, `imageIdealData_twistPairing_of_epi`, `IsHilbertFamily.imageIdealData_twistPairing_counit` | as above |
| [IdealTwist/Evaluation](IdealTwist/Evaluation.lean) | `twistedEvaluationMap_eq`, `evaluationIdeal_eq_of_epi`, `IsHilbertFamily.evaluationIdeal_eq_of_epi_homEquiv` | as above |
| [UniversalSubschemePullback](UniversalSubschemePullback.lean) | `monomialEvaluation`, `directImageMonomialMap`, `epi_directImageMonomialMap`, `directImageQuotientMap_eq_comp`, `monomialEvaluationLift`, `IsHilbertFamily.evaluationIdeal_kernel_directImageQuotientMap`, `IsHilbertFamily.universalHilbertSubscheme_comap_grassmannianMap` | any `T` for the first four; `T` locally Noetherian, natural `r ≥ m` for the last two |
| [PulledBackGrassmannianPoint](PulledBackGrassmannianPoint.lean) | `monomialEvaluation_comp_twistedRestriction_evaluationIdeal`, `comp_directImageQuotientMap_evaluationIdeal`, `IsHilbertFamily.grassmannianMap_eq_of_comap_universalHilbertSubscheme` | `K` quasi-coherent; `T` locally Noetherian for the last |
| [Representability](Representability.lean) | `hilbertScheme`, `hilbertSchemeι`, `isImmersion_hilbertSchemeι`, `exists_lift_hilbertSchemeι_iff`, `universalHilbertFamily`, `locallyNoetherianHilbertFunctorRepresentableBy`, `locallyNoetherianGrassmannianNatTrans_app_injective`, `locallyNoetherianGrassmannianNatTrans_app_homEquiv` | `A` Noetherian, natural `r ≥ m` (injectivity: any `A`) |
| [OpenSubfunctor](OpenSubfunctor.lean) | `containmentLocus`, `mem_containmentLocus`, `preimage_containmentLocus_eq_top_iff`, `openHilbertSubfunctor`, `mem_openHilbertSubfunctor_obj`, `isOpenOverSubfunctor_openHilbertSubfunctor`, `locallyNoetherianOpenHilbertSubfunctor`, `isOpenSubfunctor_locallyNoetherianOpenHilbertSubfunctor` | `[Finite ι]`, `U ⊆ P^n_A` open, any `T` over `Spec A`; no flatness of `Z`, no Noetherian hypothesis |
| [OpenSubscheme](OpenSubscheme.lean) | `openHilbertSchemeOpens`, `mem_openHilbertSchemeOpens`, `openHilbertSchemeOver`, `openHilbertScheme`, `openHilbertSchemeι`, `isOpenImmersion_openHilbertSchemeι`, `isNoetherian_openHilbertScheme`, `preimage_openHilbertSchemeOpens_eq_top_iff`, `locallyNoetherianOpenHilbertSubfunctorRepresentableBy`, `locallyNoetherianOpenHilbertSubfunctorRepresentableBy_homEquiv_coe`, `locallyNoetherianOpenHilbertSubfunctorRepresentableBy_homEquiv_id_coe` | `A` Noetherian, `e : ι ≃ Fin (n + 1)`, natural `r ≥ m`, `U ⊆ P^n_A` open |
| [ClosedSubscheme/SectionMap](ClosedSubscheme/SectionMap.lean) | `familySectionMap`, `directImageSectionMap`, `directImageSectionMap_monomialMap` (= `directImageQuotientMap`, `rfl`), `directImageSectionMap_eq_zero_iff`, `directImageSectionMap_baseChange`, `IsHilbertFamily.pullback_map_directImageSectionMap_eq_zero_iff` | any `T`, any `φ : 𝒪^J ⟶ 𝒪(r)` (the last: `T` locally Noetherian, natural `r ≥ m`) |
| [ClosedSubscheme/Containment](ClosedSubscheme/Containment.lean) | `sectionPairing` (`sectionPairing_homogeneousEvaluation`: = `homogeneousEvaluationPairing`), `familySectionPairing`, `imageIdealData_familySectionPairing`, `comap_le_iff_familySectionMap_eq_zero`, `comap_le_iff_directImageSectionMap_eq_zero` | any `T`, any closed `V`; `C` the image ideal of `sectionPairing ι r φ` |
| [ClosedSubscheme/Generation](ClosedSubscheme/Generation.lean) | `idealTwistToTwistingSheaf`, `imageIdealData_sectionPairing_of_epi`, `exists_sectionPairing_imageIdealData_eq` | the last: `A` Noetherian, `e : ι ≃ Fin (n + 1)` |
| [ClosedSubscheme/Representability](ClosedSubscheme/Representability.lean) | `closedHilbertSubfunctor` (a `Subfunctor` of `hilbertFunctor`), `locallyNoetherianClosedHilbertSubfunctor`, `closedHilbertIdeal`, `closedHilbertScheme`, `closedHilbertSchemeι`, `isNoetherian_closedHilbertScheme`, `closedHilbertSchemeOver`, `exists_lift_closedHilbertSchemeι_iff`, `locallyNoetherianClosedHilbertSubfunctorRepresentableBy` (`_homEquiv_coe`, `_homEquiv_id_coe`), `universalClosedHilbertPoint`, `exists_closedHilbertScheme_representableBy` | `A` Noetherian, natural `r ≥ hilbertRegularityBound n Φ`, `φ` cutting out `C` |
| [Immersed/Functor](Immersed/Functor.lean) | `immersionBaseChange`, `immersionBaseChange_eq_overPullbackMap`, `isPullback_immersionBaseChange_baseChangeMap`, `isProper_subschemeι_comp_snd_iff_isClosedImmersion`, `properClosedSubschemeEquiv`, `IsImmersedHilbertFamily`, `IsImmersedHilbertFamily.comap`, `immersedHilbertFunctor`, `locallyNoetherianImmersedHilbertFunctor`, `immersedHilbertSubfunctor`, `immersedHilbertFunctorIso`, `isImmersedHilbertFamily_iff_of_isClosedImmersion` | any `T`; `[IsPreimmersion i]` for the functor; `[Finite ι]` for the bijection and the isomorphism |
| [Immersed/PointPullback](Immersed/PointPullback.lean) | `locallyNoetherianImmersedHilbertFunctor_map_coe`, `locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap` | `[IsPreimmersion i]`; imports only `Immersed/Functor` |
| [Immersed/Subfunctor](Immersed/Subfunctor.lean) | `comap_fst_le_iff_exists_lift`, `comap_ker_le_of_comp_eq`, `fst_mem_coborderRange_of_comp_eq`, `exists_lift_immersionBaseChange_iff_closed_and_open`, `ker_immersionBaseChange`, `exists_lift_immersionBaseChange_iff`, `mem_immersedHilbertSubfunctor_obj_iff_closed_and_open`, `immersedHilbertSubfunctor_eq_inf`, `immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker`, `immersedHilbertSubfunctor_subschemeι`, `locallyNoetherianImmersedHilbertSubfunctor`, `locallyNoetherianImmersedHilbertFunctorIso`, `map_comap_immersionBaseChange_of_mem` | any `T`; the converse and the meet: `[IsImmersion i] [QuasiCompact i]`; the closed case: `[IsClosedImmersion i]`; the isomorphism: `[IsPreimmersion i] [Finite ι]` |
| [Immersed/Representability](Immersed/Representability.lean) | `immersedHilbertSchemeOpens`, `immersedHilbertSchemeOver`, `immersedHilbertScheme`, `immersedHilbertSchemeι`, `isImmersion_immersedHilbertSchemeι`, `isNoetherian_immersedHilbertScheme`, `immersedHilbertSchemeToHilbertScheme`, `exists_lift_immersedHilbertSchemeι_iff`, `locallyNoetherianImmersedHilbertSubfunctorRepresentableBy`, `locallyNoetherianImmersedHilbertFunctorRepresentableBy` (`_homEquiv_coe`, `_homEquiv_eq_comap`), `universalImmersedHilbertFamily`, `universalImmersedHilbertPoint`, `isImmersedHilbertFamily_universalImmersedHilbertFamily`, `map_universalImmersedHilbertFamily`, `exists_immersedHilbertScheme_representableBy` | `A` Noetherian, `e : ι ≃ Fin (n + 1)`, `[IsImmersion i]`, natural `r ≥ hilbertRegularityBound n Φ`, any `φ`; `hC` (`φ` cuts out `i.ker`) only for the lifting criterion, the representations, the universal point and the statements about the universal family |
| [Immersed/QuasiProjective](Immersed/QuasiProjective.lean) | `isHQuasiProjective_immersedHilbertSchemeOver_hom` | `A` Noetherian, `[IsImmersion i]`, any `φ` |
| [Immersed/ClosedImmersion](Immersed/ClosedImmersion.lean) | `immersedHilbertSubfunctorIsoClosedHilbertSubfunctor`, `locallyNoetherianImmersedHilbertFunctorIsoOfIsClosedImmersion`, `isHQuasiProjective_closedHilbertSchemeOver_hom`, `locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion` (`_homEquiv_coe`, `_homEquiv_coe_map`, `_homEquiv_id_coe`), `exists_locallyNoetherianImmersedHilbertFunctor_representableBy_of_isClosedImmersion` | `i` a closed immersion; the isos: `[Finite ι]` for the restricted one; the rest: `A` Noetherian, `e : ι ≃ Fin (n + 1)`, natural `r ≥ hilbertRegularityBound n θ`, `φ` with `imageIdealData (sectionPairing ι r φ) = i.ker` |
| [Immersed/Fiber](Immersed/Fiber.lean) | `isPullback_embeddedFiberι_pointMap`, `comap_pointMap_map_immersionBaseChange`, `isClosedImmersion_comap_subschemeι_comp_embeddedFiberι`, `subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange`, `eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange`, `flat_map_immersionBaseChange_subschemeι_comp_snd`, `isIso_idealPullbackMap_fieldPoint`, `fieldPointIdealPullbackIso`, `eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_of_flat`, `subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_eq_sub` | field point `x : Spec K ⟶ T` at a variable field, any `T`; the square: any `i`; the image: `[IsPreimmersion i]`, `V` closed in `P_T`; the Euler-characteristic formula: closed immersion `i`, `e : ι ≃ Fin (N + 1)`, any closed `V`; flatness of the image: any `hi`; the pulled-back ideal and `ψ − φ₀`: `V` flat over `T` |
| [Divisor/Functor](Divisor/Functor.lean) | `IsRelativeDivisorFamily` (`.flat`, `.isHilbertFamily_map`, `.isClosedImmersion`, `.comap`, `.of_isRelativeEffectiveCartier`), `isRelativeDivisorFamily_iff_of_isClosedImmersion`, `relativeDivisorFunctor` (`_map_coe`), `locallyNoetherianRelativeDivisorFunctor`, `relativeDivisorSubfunctor` (a `Subfunctor` of `immersedHilbertFunctor`), `relativeDivisorFunctorObjEquiv`, `relativeDivisorFunctorIso` | `i : X ⟶ P^n_A` a preimmersion over `Spec A`, any `T`; the closed forms: `[IsClosedImmersion i] [Finite ι]` |
| [Divisor/Representability](Divisor/Representability.lean) | `locallyNoetherianRelativeDivisorSubfunctor`, `divisorLocus`, `mem_divisorLocus`, `preimage_divisorLocus_eq_top_iff`, `isOpenSubfunctor_locallyNoetherianRelativeDivisorSubfunctor`, `preimage_divisorLocus_homEquiv_id_eq_top_iff`, `divisorSchemeOver`, `divisorScheme`, `divisorSchemeι`, `isOpenImmersion_divisorSchemeι`, `divisorSchemeToHilbertScheme`, `locallyNoetherianRelativeDivisorFunctorRepresentableBy` (`_homEquiv_coe`, `_homEquiv_coe_eq_comap`), `universalDivisor`, `isRelativeEffectiveCartier_universalDivisor`, `universalDivisor_eq`, `isHQuasiProjective_divisorSchemeOver_hom`, `isNoetherian_divisorScheme` (`_of_isHQuasiProjective`) | `[Finite ι]`, `i` a closed immersion, `[Flat πX]`, locally Noetherian test schemes; any representation `E` of `Hilb^θ_X` by `H`; H-qp: `A` Noetherian and `H` H-qp |
| [Divisor/ClosedHilbertScheme](Divisor/ClosedHilbertScheme.lean) | `exists_locallyNoetherianRelativeDivisorFunctor_representableBy` | `A` Noetherian, `e : ι ≃ Fin (n + 1)`, `i` a closed immersion, `[Flat πX]` |
| [Quotient/Datum](Quotient/Datum.lean) | `QuotientHilbertDatum`, `QuotientHilbertDatum.familyProj`, `exists_lift_comap_iff_exists_lift`, `exists_lift_subschemeι_iff_pointsRelation`, `pointsRelation_iff_exists_lift_comap`, `ker_comap_eq_comap`, `pointsRelation_of_comp_familyProj_eq`; `CategoryTheory.pointsRelation_comp_fst_comp_snd_iff` | any base `S`, any `T`; `j` a closed immersion |
| [Quotient/Points](Quotient/Points.lean) | `QuotientHilbertDatum.pointsRelation_iff_comp_eq` | `T` locally Noetherian, `πZ` locally of finite type, the relation an equivalence relation on locally Noetherian points |
| [Quotient/Graph](Quotient/Graph.lean) | `QuotientHilbertDatum.graph`, `isClosedImmersion_graph`, `exists_comp_subschemeι_eq_graph`, `isClosedImmersion_of_comp_subschemeι_eq_graph`, `comp_familyProj_of_comp_subschemeι_eq_graph`, `exists_comp_eq_iff_of_comp_subschemeι_eq_graph`, `ker_comap_fst_eq_ker_comap_snd_of_comp_subschemeι_eq_graph` | `isClosedImmersion_graph`, `isClosedImmersion_of_comp_subschemeι_eq_graph`: `H` separated over `S`; `exists_comp_subschemeι_eq_graph`: `j` a closed immersion, `(𝟙, 𝟙)` related at `T = Z`; the last: `j` a closed immersion, `πZ` locally of finite type, `H` separated over `S` and locally Noetherian, the relation an equivalence relation on locally Noetherian points; the `…_of_comp_subschemeι_eq_graph` statements take any `Γ` with `Γ ≫ D.subschemeι = graph` |
| [Quotient/Descent](Quotient/Descent.lean) | `QuotientHilbertDatum.isPullback_toImage_of_comp_subschemeι_eq_graph`, `exists_isPullback_toImage`, `flat_toImage`, `surjective_toImage`, `isProper_toImage` | as `ker_comap_fst_eq_ker_comap_snd_of_comp_subschemeι_eq_graph`; all but `isPullback_toImage_of_comp_subschemeι_eq_graph` also need `Z` locally Noetherian |
| [Quotient/FlatProper](Quotient/FlatProper.lean) | `FlatProperQuotient`, `quasiCompact`, `isLocallyNoetherian`, `locallyOfFinitePresentation`, `isSeparated`, `locallyOfFiniteType`, `effectiveEpi`, `isColimitCofork`, `singleton_mem_fppfPrecoverage` | base `Spec A`; Noetherian `A` for local Noetherianity, finite presentation and fppf |
| [Quotient/Effective](Quotient/Effective.lean) | `QuotientHilbertDatum.comp_toImage_eq`, `isIso_lift_toImage`, `isPullback_toImage`, `flatProperQuotient`, `flatProperQuotient_q`, `flatProperQuotient_q_imageι`, `nonempty_flatProperQuotient_of_comp_eq` | `comp_toImage_eq`: `j` a closed immersion, `Z` locally Noetherian, `πZ` locally of finite type, the relation an equivalence relation on locally Noetherian points; `isIso_lift_toImage`, `isPullback_toImage`: as Descent; `flatProperQuotient` and the last three: base `Spec A`, `H` H-quasi-projective and locally Noetherian |
| [Nonempty](Nonempty.lean) | `subschemeHilbertPolynomial_eq_zero_iff`, `subschemeHilbertPolynomial_ne_zero_iff`, `subschemeHilbertPolynomial_top`, `nonempty_subscheme_comap_pointMap_iff`, `nonempty_subscheme_comap_fromSpecResidueField_iff`, `IsHilbertFamily.surjective_of_ne_zero`, `IsHilbertFamily.ne_zero_of_nonempty`, `IsHilbertFamily.surjective_iff_ne_zero`, `fiberHilbertPolynomialAt_quotientModule_eq_zero_iff`, `fiberHilbertPolynomialAt_quotientModule_ne_zero_iff` | `subschemeHilbertPolynomial_eq_zero_iff`, `_ne_zero_iff`: field `K`, `e : ι ≃ Fin (n + 1)`; `_top`: field `K`, any `ι`; `nonempty_subscheme_comap_*_iff`: any `ι`, `T`, closed `Z` (any ring `K` for `pointMap`); `IsHilbertFamily.*`, `fiberHilbertPolynomialAt_quotientModule_*_iff`: `e`, any `T`; no flatness or Noetherian hypothesis |
| [Coproduct/Decomposition](Coproduct/Decomposition.lean) | `isHilbertFamily_comap_pullbackBaseChange_of_flat`, `isHilbertFamily_comap_flatteningStratumι`, `isOpenImmersion_flatteningStratumι_of_flat`, `isClopen_setOf_fiberHilbertPolynomialAt_quotientModule_eq_of_flat`, `isIso_sigmaDesc_flatteningStratumι_of_flat`, `fiberHilbertPolynomialAt_pullback_baseChangeMap`, `fiberHilbertPolynomialAt_quotientModule_comap_baseChangeMap`, `pullbackSigmaι_toSpec_eq_baseChangeMap`, `fiberHilbertPolynomialAt_sigmaGlue_sigmaι`, `fiberHilbertPolynomialAt_sigmaGlue_sigmaι_of_isHilbertFamily`, `fiberHilbertPolynomialAt_sigmaGlue_comap_eq_iff` | `[Finite ι]`; restriction along a map with constant fibre polynomial: `V` flat, any `T`; stratum restriction: `T` locally Noetherian, `e`, any `V`; decomposition: `T` locally Noetherian, `e`, `V` flat, `φ` injective; glued family: any small `J` (`_comap_eq_iff`: `Φ` injective) |
| [Coproduct/Family](Coproduct/Family.lean) | `Scheme.IdealSheafData.sigmaGlue_iff`, `flat_sigmaGlue`, `isProper_sigmaGlue`, `surjective_sigmaGlue` | any `πZ : Z ⟶ S`, `πH j : H j ⟶ S`, `J` small; `sigmaGlue_iff`: `P` local at the target |

**The functor.** `IsHilbertFamily ι Φ g Z` asks a closed subscheme `Z ⊆ P^n_A ×_{Spec A} T` to be
flat over `T` (Mathlib's `Flat` of `Z ⟶ T`; equivalently `𝒪_Z` is relatively flat,
`relativeFlat_quotientModule_iff_flat` in
[Modules/Flat/Relative/ClosedSubscheme](../Modules/Flat/Relative/ClosedSubscheme.lean)) and its
fiber `Z.comap (pointMap ι g x)` at every field point `x : Spec K ⟶ T` to have Hilbert polynomial
`Φ`. `hilbertFunctor ι Φ` acts by `comap` along `baseChangeMap`; the point and base-change maps
are [ProjectiveSpace/BaseChange/Point](../ProjectiveSpace/BaseChange/Point.lean). The field-point
condition is equivalent to the residue-field condition of Nitsure (`isHilbertFamily_iff_residueField`).
The functor is defined on all schemes over `Spec A`; Nitsure's statements restrict it to locally
Noetherian test schemes.

**Uniform regularity and direct images.** `hilbertRegularityBound n Φ` is Mumford's bound at the
binomial coefficients of `r ↦ C(r + n, n) - Φ(r)` (unique by `Int.eq_of_forall_sum_mul_choose_eq`,
[RingTheory/Binomial/Uniqueness](../../RingTheory/Binomial/Uniqueness.lean)); it depends only on
`n` and `Φ`, is at least `n + 2`, and makes every fiber ideal `m`-regular. Over a Noetherian `B`,
for `r ≥ m`: `H^q(I_Z(r)) = H^q(𝒪_Z(r)) = 0` for `q ≥ 1`, the `H^0` are projective, commute with
every base change, have ranks `C(r + n, n) - Φ(r)` and `Φ(r)`, and
`0 → H^0(I_Z(r)) → H^0(𝒪(r)) → H^0(𝒪_Z(r)) → 0` is exact; `I_Z(r)` is globally generated, so the
sections determine `Z`. The fibers of `𝒪_Z(r)` use the isomorphism `quotientModulePullbackIso`
of [IdealSheaf/BaseChange/QuotientModule](../IdealSheaf/BaseChange/QuotientModule.lean), which
needs no flatness.

**The Grassmannian point.** For a natural `r ≥ m`, `grassmannianPoint` is the kernel of
`H^0(𝒪(r)) ↠ H^0(𝒪_Z(r))`, a point of Mathlib's quotient-convention Grassmannian
`G(⌊Φ(r)⌋₊, H^0(P^n_B, 𝒪(r)); B)`. `unitTwistH0Equiv : B ⊗[A] A[x]_r ≃ₗ[B] H^0(P^n_B, 𝒪(r) ⊗ 𝒪)`
moves it into `(Module.Grassmannian.functor ⌊Φ(r)⌋₊).obj B` (`grassmannianFunctorPoint`). The
points are injective (`eq_of_grassmannianFunctorPoint_eq`) and natural in `B`
(`map_grassmannianFunctorPoint`): base change of the point of `Z` along `f : B → B'` is the point
of the pullback of `Z`. The proof reduces to `f ⊗ id` mapping the kernel at `B` into the kernel at
`B'` (`Module.Grassmannian.map_eq_of_forall`), which is the base change of homogeneous polynomial
sections ([ProjectiveSpace/BaseChange/HomogeneousSections](../ProjectiveSpace/BaseChange/HomogeneousSections.lean))
and of the restriction to `Z`. Together they form `noetherianAffineGrassmannianNatTrans` on the
full subcategory of Noetherian `A`-algebras; through the monomial basis `A[x]_r ≅ A^N`,
`N = (n + r).choose r`, `noetherianAffineGrassmannianNatTransFin` takes values in the functor
`Module.Grassmannian.functor ⌊Φ(r)⌋₊ (Fin N → A)` used by `Grassmannian.localFunctor`.

**The image step.** `exists_lift_flatteningStratumι_iff_isHilbertFamily` is property (F) of
Nitsure, §5, p. 26, with `E = O_X`: for locally Noetherian `S` and `T`, a morphism `g : T ⟶ S`
factors through the flattening stratum `S_Φ` of `𝒪_Z` exactly when
`Z.comap (pullbackBaseChange ι s g)` is a point of `Hilb^Φ(T)`. No flatness of `Z` is assumed,
since `F_T ≅ 𝒪_{Z_T}` holds for every base change (`quotientModulePullbackIso`), and the coherence
premise `hF` holds for every `Z` (`affineLocallyFiniteType_quotientModule`).

**The point over locally Noetherian `T`.** On `X_T = P^n_A ×_{Spec A} T`, `𝒪_Z(r)` is
`fst^*𝒪(r) ⊗ 𝒪_Z` (`familyQuotientTwist`, with `𝒪(r)` from
[ProjectiveSpace/BaseChange/FamilyTwist](../ProjectiveSpace/BaseChange/FamilyTwist.lean)). For a
point `Z` of `Hilb^Φ(T)`, `T` locally Noetherian and a natural `r ≥ m`, the direct image
`π_*𝒪_Z(r)` is finite locally free of rank `⌊Φ(r)⌋₊` by geometric concentration
(`Cohomology/BaseChange/NoetherianPushforward`), the local freeness part of (*) of Nitsure, §5,
p. 25; it commutes with every base change, which Nitsure derives from (*) by Theorem 3.7. The
evaluation map `𝒪_T^{monomials} ⟶ π_*𝒪_Z(r)` (`directImageQuotientMap`) is the adjoint of the
pulled-back monomial sections (`monomialMap` of
[ProjectiveSpace/HomogeneousEvaluation](../ProjectiveSpace/HomogeneousEvaluation.lean)) restricted
to `Z`. It is an epimorphism: on an affine open `Spec B` it becomes
`𝒪^N ⟶ (toSpec)_*𝒪(r) ⟶ (toSpec)_*𝒪_{Z_x}(r)`, both onto on global sections
([Cohomology/Projective/GlobalSections/DirectImage](../Cohomology/Projective/GlobalSections/DirectImage.lean)
and `epi_pushforward_twistedRestriction`). Its classifying map is `IsHilbertFamily.grassmannianMap`.
Naturality comes from the cartesian base-change mate of `isPullback_baseChangeMap`, which is
invertible ([Modules/BaseChange/CartesianInvertibility](../Modules/BaseChange/CartesianInvertibility.lean)),
so no affine quotients are glued. On the test category `Scheme.LocallyNoetherianOver (Spec A)`
([Properties/Noetherian/LocallyNoetherianOver](../Properties/Noetherian/LocallyNoetherianOver.lean))
these points form the natural transformation `locallyNoetherianGrassmannianNatTrans`, the morphism
`α : Hilb^Φ → Grass` of Nitsure, p. 26.

**The universal subscheme.** For `ιK : K ⟶ 𝒪_T^I` and homogeneous polynomials `s : I → A[x]_r`,
`evaluationIdeal ι g r s ιK` is the image ideal (`Hom.imageIdealData`) of
`π^*K ⊗ p^*𝒪(-r) ⟶ p^*𝒪^I ⊗ p^*𝒪(-r) ⟶ 𝒪` on `X_T`, the second map the pullback of the
evaluation `𝒪^I ⊗ 𝒪(-r) ⟶ 𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` (`homogeneousEvaluationPairing`); for quasi-coherent
`K` it is the image of `h(-r)` for the map `h` of Nitsure's property (F) (§5, p. 26), with
`E = 𝒪_X`. It commutes with every base change of `T` for quasi-coherent `K`
(`evaluationIdeal_comap_baseChangeMap`), because the image ideal of a module-to-unit map commutes
with every pullback (`Hom.imageIdealData_pullback`,
[Modules/ZeroLocus/Pullback](../Modules/ZeroLocus/Pullback.lean)). Over the Grassmannian of
rank-`k` quotients of the free sheaf on the monomials of degree `r`,
`universalHilbertSubscheme = Z(K_univ)` pulls back along the classifying map of a quotient `q` to
`Z(ker q)` (`universalHilbertSubscheme_comap_classifyingMap`).

**The twisted ideal sheaf.** The `IdealTwist/` leaves of the table treat
`I_Z(r) = p^*𝒪(r) ⊗ I_Z` (`familyIdealTwist`, `IdealTwist/Family`). For a point `Z` of `Hilb^Φ(T)` it is flat over `T`
for every `T`; over a locally Noetherian `T` and for natural `r ≥ m` its geometric fibres are
concentrated in degree zero, so `π_* I_Z(r)` is finite locally free of rank
`C(n + r, r) - ⌊Φ(r)⌋₊`, commutes with every base change and is the kernel of
`π_*(𝒪(r) ⊗ 𝒪) ⟶ π_* 𝒪_Z(r)`. The counit `π^*π_* I_Z(r) ⟶ I_Z(r)` is an epimorphism (relative
global generation, from Lemma 2.1 (c) on affine pieces; `IdealTwist/GlobalGeneration`), and `Z` is
the image ideal of `π^*π_* I_Z(r) ⊗ 𝒪(-r) ⟶ 𝒪` (`IdealTwist/Untwist`, `IdealTwist/Evaluation`).
This proves the local freeness and counit parts of (*) for `G = I_Z`, and base change; the
vanishing `R^i π_* I_Z(r) = 0` is not stated.

**Representability.** For a Noetherian ring `A` and a natural `r ≥ m`, the Hilbert scheme
`hilbertScheme ι n e A Φ r` is the flattening stratum with polynomial `Φ` of the structure module
of the universal subscheme `Z_univ` over the Noetherian Grassmannian `G` of rank-`⌊Φ(r)⌋₊`
quotients of `𝒪^N`, `N = (n + r).choose r`; it is a locally closed subscheme of `G`
(`isImmersion_hilbertSchemeι`) and Noetherian (`isNoetherian_hilbertScheme`). It represents the
Hilbert functor on locally Noetherian test schemes (`locallyNoetherianHilbertFunctorRepresentableBy`),
with universal family `Z_univ|_{G_Φ}` (`universalHilbertFamily`). This is Nitsure, §5,
Theorem 5.3 (p. 24; the locally closed form is reached on p. 27) with `X = P^n_A` and `E = 𝒪`,
through the proof of Theorem 5.2 (p. 24), with the test
schemes of §1, pp. 3–4; projectivity is not claimed. "⇒": `Z = Z_univ.comap φ_Z`
(`IsHilbertFamily.universalHilbertSubscheme_comap_grassmannianMap`), since `Z(ker q_Z) = Z` by
relative global generation of `I_Z(r)` and the epimorphism `𝒪^{monomials} ⟶ π_*(𝒪(r) ⊗ 𝒪)`
(`UniversalSubschemePullback`). "⇐": if `Z_univ.comap φ ∈ Hilb^Φ(T)` then its point is `φ`
(`IsHilbertFamily.grassmannianMap_eq_of_comap_universalHilbertSubscheme`,
`PulledBackGrassmannianPoint`): the kernel `φ^* K_univ` vanishes on `π_* 𝒪_{Z_T}(r)` (untwisting
through `𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪`), and a surjection between locally free quotients of the same rank is
an isomorphism. Nitsure states the representing property "by its construction" (p. 27); this
equal-rank argument supplies it. The Grassmannian points are injective for every ring `A`
(`locallyNoetherianGrassmannianNatTrans_app_injective`) and correspond to `G_Φ ⟶ G` under the
representing isomorphism (`locallyNoetherianGrassmannianNatTrans_app_homEquiv`).

**Closed subschemes.** For a closed `C ⊆ P^n_A` (not necessarily flat) the Hilbert subfunctor of
`C` (`closedHilbertSubfunctor ι Φ C`, a Mathlib `Subfunctor`) consists of the points `V ⊆ C_T`, written
`C.comap p ≤ V` with `C_T = C.comap p`, the closed subscheme cut out by the image of
`p^* I_C ⟶ 𝒪` (Stacks, Tag 01JU (1)). Choose `φ : 𝒪^J ⟶ 𝒪(r)` whose section pairing
`𝒪^J ⊗ 𝒪(-r) ⟶ 𝒪` has image ideal `C` (for `r ≥` the regularity of `I_C`,
`exists_sectionPairing_imageIdealData_eq`, Nitsure Lemma 2.1 (c)). Then `V ⊆ C_T` iff the images
of the sections of `φ` vanish in `π_* 𝒪_V(r)` (`comap_le_iff_directImageSectionMap_eq_zero`, no
flatness). Over the Hilbert scheme these images form a map `𝒪^J ⟶ π_* 𝒪_W(r)` into a finite
locally free sheaf of rank `⌊Φ(r)⌋₊`, compatible with base change for Hilbert families
(`IsHilbertFamily.pullback_map_directImageSectionMap_eq_zero_iff`), and its zero scheme
(`Modules/ZeroLocus/LocallyFree`) is the closed subscheme `closedHilbertScheme` of
`hilbertScheme` (Noetherian), which represents the Hilbert subfunctor of `C` on locally Noetherian
test schemes (`locallyNoetherianClosedHilbertSubfunctorRepresentableBy`, universal family
`…_homEquiv_id_coe`, `universalClosedHilbertPoint`). This is Nitsure, Theorem 5.3, p. 24, for
`X = C` and `E = 𝒪_C` (Theorem 6.1, p. 28, for closed `X`), by the closed embedding of Lemma 5.4
(ii), p. 25; the vanishing scheme of Remark 3.6, p. 17 is replaced by the Fitting zero scheme of
`Modules/ZeroLocus/LocallyFree`.

**Open subschemes of `P^n_A`.** For an open `U ⊆ P^n_A` and `g : T ⟶ Spec A`, a closed subscheme
`Z ⊆ P^n_A ×_{Spec A} T` lies in `U_T` when every point of its support maps into `U`. For finite
`ι` this is an open and universal condition on `T`: `containmentLocus ι g Z U` is the complement
of the image of the closed set `Z ∖ U_T` under the proper projection to `T`
(`Scheme.Hom.complImage`, [Morphisms/UniversallyClosed/ImageComplement](../Morphisms/UniversallyClosed/ImageComplement.lean)),
and `f : T' ⟶ T` over `Spec A` factors through it exactly when the pullback of `Z` lies in
`U_{T'}` (`preimage_containmentLocus_eq_top_iff`; images commute with base change on points,
Stacks 01JT). No flatness and no Noetherian hypothesis is used. Hence the subfunctor `Hilb^Φ_U`
of the families contained in `U` (`openHilbertSubfunctor`, on all schemes over `Spec A`) is open
(`isOpenOverSubfunctor_openHilbertSubfunctor`; Stacks 01JI), also on locally Noetherian test
schemes. For a Noetherian `A` it is represented on locally Noetherian test schemes by the open
subscheme `G_Φ^U = openHilbertScheme ι n e A Φ r U` of `G_Φ` over which the universal family lies
in `U` (`locallyNoetherianOpenHilbertSubfunctorRepresentableBy`), with universal family the
restriction of `universalHilbertFamily`; `openHilbertSchemeι` is an open immersion and `G_Φ^U` is
Noetherian. This is Nitsure, §6, p. 28, Exercise A for `π : P^n_A ×_{Spec A} G_Φ ⟶ G_Φ`,
`Y = (P^n_A ∖ U)_{G_Φ}` and `F = 𝒪_W`, the openness step of the proof of Theorem 6.1; the
representation is the restriction of `locallyNoetherianHilbertFunctorRepresentableBy` to an open
subscheme (`Scheme.LocalRepresentability.representableByRestrictOpens`,
[Sites/OverRepresentability/OpenSubscheme](../Sites/OverRepresentability/OpenSubscheme.lean)).

**The Hilbert functor of an immersed scheme.** For a preimmersion (for example an immersion)
`i : Y ⟶ P^n_A` over `Spec A` and `i_T = immersionBaseChange i hi g : Y ×_{Spec A} T ⟶
P^n_A ×_{Spec A} T` (Mathlib's `((Over.pullback g).map (Over.homMk i hi)).left`),
`immersedHilbertFunctor i hi Φ` assigns to `T` the closed subschemes `V` of `Y ×_{Spec A} T` that
are proper over `T` and whose image `V.map i_T` is a point of `Hilb^Φ(T)`: Nitsure's
`Hilb^{Φ,L}_{Y/S}` (§1, pp. 3–4) for `L = i^*𝒪(1)`, the setting of Thm 6.1 (p. 28) with trivial
bundles. With finitely many coordinates it is isomorphic to the subfunctor
`immersedHilbertSubfunctor i hi Φ` of `hilbertFunctor ι Φ` of the families whose inclusion factors
through `i_T` (`immersedHilbertFunctorIso`), by `V ↦ V.map i_T` with inverse `W ↦ W.comap i_T`
(`properClosedSubschemeEquiv`, [IdealSheaf/Monomorphism](../IdealSheaf/Monomorphism.lean)).
Nitsure uses this identification implicitly, for closed subschemes (p. 25, after Lemma 5.4) and for
open subschemes of a proper scheme (the second Exercise on p. 28); the one-step comparison along
`i_T` is a route choice. For a closed immersion `i` properness is automatic
(`isImmersedHilbertFamily_iff_of_isClosedImmersion`).

**Locally closed subschemes of `P^n_A`.** For an immersion `i : Y ⟶ P^n_A` over `Spec A`, let
`C = i.ker` be its scheme-theoretic image and `U = i.coborderRange`. A family of `Hilb^Φ` contained
in `Y` lies in `C_T` and in `U_T`, and for a quasi-compact `i` the converse holds, through Mathlib's
cartesian square `Y = im(i) ×_P U` (`IsImmersion.isPullback_toImage_liftCoborder`); so
`immersedHilbertSubfunctor i hi Φ = closedHilbertSubfunctor ι Φ C ⊓ openHilbertSubfunctor ι Φ U`
(`immersedHilbertSubfunctor_eq_inf`, [Immersed/Subfunctor](Immersed/Subfunctor.lean)). For a closed
immersion the open condition is void and the families contained in `Y` are `Hilb^Φ_C`
(`immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker`). On locally Noetherian test schemes the
Hilbert functor of `Y` acts by pullback along `Y ×_{Spec A} Z ⟶ Y ×_{Spec A} T`, so every
representation pulls back its universal family
(`locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap`,
[Immersed/PointPullback](Immersed/PointPullback.lean), a leaf directly above the functor). For a
Noetherian `A` every immersion into `P^n_A` is quasi-compact, and with sections `φ` of `𝒪(r)` cutting out `C` the open subscheme
`H^Φ_Y = immersedHilbertScheme ι n e A Φ r hr φ i` of the closed `H_C` over which the universal
family lies in `U` (the preimage of `openHilbertSchemeOpens`) represents the Nitsure-form Hilbert
functor `locallyNoetherianImmersedHilbertFunctor i hi Φ` on locally Noetherian test schemes
(`locallyNoetherianImmersedHilbertFunctorRepresentableBy`; Nitsure, Thm 6.1, p. 28, for
`E = 𝒪_Y`), with universal family `universalImmersedHilbertFamily ⊆ Y ×_{Spec A} H^Φ_Y`, a point of
that functor whose pullbacks are the points of `H^Φ_Y` and whose image in `P^n_A ×_{Spec A} H^Φ_Y` is
the restricted universal family of `G_Φ`; a morphism `T ⟶ G_Φ` factors through `H^Φ_Y` exactly when
its family is contained in `Y` (`exists_lift_immersedHilbertSchemeι_iff`). Such `φ` exist for all
large `r` (`exists_sectionPairing_imageIdealData_eq`; packaged in
`exists_immersedHilbertScheme_representableBy`). `immersedHilbertSchemeι : H^Φ_Y ⟶ G_Φ` is an
immersion, so `H^Φ_Y` is H-quasi-projective over `Spec A`
(`isHQuasiProjective_immersedHilbertSchemeOver_hom`,
[Immersed/QuasiProjective](Immersed/QuasiProjective.lean)). The route is Nitsure's: the Hilbert
functor of `Y` is open in that of its schematic closure (p. 28, the two Exercises), which is closed
in `Hilb^Φ` (p. 25, Lemma 5.4 (ii)).

**The quotient by a flat proper equivalence relation.** The `Quotient/` leaves prove the core of
Nitsure, Theorem 6.8 (pp. 33–35; Theorem 6.9, p. 36), against an abstract Hilbert datum
`QuotientHilbertDatum πZ j` for `πZ : Z ⟶ S` and a closed immersion `j : R ⟶ Z ×_S Z`: a scheme
`H` over `S`, a closed subscheme `D ⊆ Z ×_S H` flat, proper and surjective over `H`, and
`φ : Z ⟶ H` over `S` with `D.comap (𝟙 × φ) = ker j` (Nitsure's `φ^* D = R`), such that points of
`H` over `S` on locally Noetherian `T` are determined by their pulled-back families on `Z ×_S T`.
No Hilbert scheme is unfolded; the instantiation with the finite union of Hilbert schemes of `Z`
is separate. With `p₁ = j ≫ pr₁`, `p₂ = j ≫ pr₂` and the relation an equivalence relation on
locally Noetherian points (`Properties/Noetherian/EquivalenceRelation`): `(x, y) ∈ R(T)` iff
`(x, φ ∘ y) ∈ D(T)` for every `T`, and iff `φ ∘ x = φ ∘ y` for `T` locally Noetherian (`(***)`,
p. 34); the graph `(𝟙, φ)` factors through `D` as a closed subscheme `Γ_φ` with
`p₁⁻¹Γ_φ = p₂⁻¹Γ_φ ⊂ D ×_H D` (pp. 34–35); by Lemma 6.7(2)
([Descent/IdealSheaf/FaithfullyFlat](../Descent/IdealSheaf/FaithfullyFlat.lean)) the
scheme-theoretic image `Q = φ.image` satisfies `Γ_φ = p⁻¹Q`, so `q = φ.toImage` is flat,
surjective and proper (p. 35, (ii)); and `(p₁, p₂) : R ⟶ Z ×_Q Z` is an isomorphism (p. 35, (iii)).
The equalities and the isomorphism are tested on locally Noetherian points
([Properties/Noetherian/Yoneda](../Properties/Noetherian/Yoneda.lean)), where Nitsure tests all
`S`-schemes. Over `Spec A` with `H` H-quasi-projective and locally Noetherian the result is a
`FlatProperQuotient`: `Q` H-quasi-projective, `q` flat, surjective and proper over `Spec A`,
`IsPullback p₁ p₂ q q`; `q` is an effective epimorphism and a coequalizer of `p₁, p₂`, and for `A`
Noetherian `Q` is locally Noetherian and `{q}` is an fppf covering.

**Coproducts of Hilbert data.** For a closed `V ⊆ P^n_A ×_{Spec A} T` flat over a
locally Noetherian `T`, `T` is the disjoint union of the open and closed strata
`T_Φ = {t | P_t = Φ}` (`Coproduct/Decomposition`, from
[FlatteningStratification/FlatDecomposition](../FlatteningStratification/FlatDecomposition.lean)),
over any injective family of polynomials containing those that occur; the restriction of `V` to
`T_Φ` (or to any open or test scheme on which `P_t = Φ`) is a point of `Hilb^Φ`, and fibre
polynomials are unchanged by pullback. Families `D j ⊆ Z ×_S H j` glue to
`sigmaGlue πZ πH D ⊆ Z ×_S ∐ H` ([IdealSheaf/GlueCoproduct](../IdealSheaf/GlueCoproduct.lean)),
flat, proper or surjective over `∐ H` exactly when every `D j` is (`Coproduct/Family`); in `P^n`
the glued family of points `D j ∈ Hilb^{Φ j}(H j)` has fibre polynomial `Φ j` on the `j`-th
component, and, for distinct `Φ j`, its pullback along `a : T ⟶ ∐ H` has fibre polynomial `Φ j`
exactly over `a⁻¹(H j)`. This is the finite union `H = ⊔ Hilb^Φ` with its family `D` of Nitsure,
proof of Thm 6.8, p. 33. No finiteness is assumed: the index types are arbitrary small types.

**Nonempty fibres.** A closed subscheme of `P^n_K` has zero Hilbert polynomial iff it
is empty (`Nonempty`); so a point of `Hilb^Φ(T)` with `Φ ≠ 0` is surjective over `T`
(`IsHilbertFamily.surjective_of_ne_zero`), and a nonempty point has `Φ ≠ 0`
(`IsHilbertFamily.ne_zero_of_nonempty`) (Nitsure, p. 33, used there without proof).

**Lower owners.** The general helpers of this family live in sibling leaves:
[IdealSheaf/QuotientModule](../IdealSheaf/QuotientModule.lean),
[IdealSheaf/Order](../IdealSheaf/Order.lean), [IdealSheaf/Comap](../IdealSheaf/Comap.lean),
[IdealSheaf/BaseChange/QuotientModule](../IdealSheaf/BaseChange/QuotientModule.lean),
[Modules/Flat/Relative/ClosedSubscheme](../Modules/Flat/Relative/ClosedSubscheme.lean),
[Modules/Pullback/Tensor/RightUnit](../Modules/Pullback/Tensor/RightUnit.lean),
[Cohomology/Modules/UnitHom](../Cohomology/Modules/UnitHom.lean),
[Cohomology/Modules/DegreeZero](../Cohomology/Modules/DegreeZero.lean),
[Cohomology/Projective/GlobalSections/PolynomialSections](../Cohomology/Projective/GlobalSections/PolynomialSections.lean),
[RingTheory/MvPolynomial/HomogeneousFinrank](../../RingTheory/MvPolynomial/HomogeneousFinrank.lean),
[RingTheory/MvPolynomial/HomogeneousBaseChange](../../RingTheory/MvPolynomial/HomogeneousBaseChange.lean),
[RingTheory/Spectrum/Prime/FreeLocus/ResidueField](../../RingTheory/Spectrum/Prime/FreeLocus/ResidueField.lean),
[RingTheory/MvPolynomial/GradedMapBasis](../../RingTheory/MvPolynomial/GradedMapBasis.lean),
[ProjectiveSpace/Monomials](../ProjectiveSpace/Monomials.lean),
[ProjectiveSpace/HomogeneousEvaluation](../ProjectiveSpace/HomogeneousEvaluation.lean),
[ProjectiveSpace/BaseChange/FamilyTwist](../ProjectiveSpace/BaseChange/FamilyTwist.lean),
[ProjectiveSpace/BaseChange/MonomialMap](../ProjectiveSpace/BaseChange/MonomialMap.lean),
[Cohomology/Projective/GlobalSections/DirectImage](../Cohomology/Projective/GlobalSections/DirectImage.lean),
[IdealSheaf/BaseChange/TwistedRestriction](../IdealSheaf/BaseChange/TwistedRestriction.lean),
[Modules/ZeroLocus/ImageFactorisation](../Modules/ZeroLocus/ImageFactorisation.lean),
[Modules/ZeroLocus/Pullback](../Modules/ZeroLocus/Pullback.lean),
[Modules/Pullback/FreeTransfer](../Modules/Pullback/FreeTransfer.lean),
[Modules/Pullback/FreeMap](../Modules/Pullback/FreeMap.lean),
[Modules/Pullback/UnitSections](../Modules/Pullback/UnitSections.lean),
[Modules/Pullback/Tensor/Pairing](../Modules/Pullback/Tensor/Pairing.lean),
[Modules/BaseChange/FreeMap](../Modules/BaseChange/FreeMap.lean),
[Modules/BaseChange/CartesianInvertibility](../Modules/BaseChange/CartesianInvertibility.lean),
[Modules/BaseChange/Counit](../Modules/BaseChange/Counit.lean),
[Modules/Generators/Counit](../Modules/Generators/Counit.lean),
[Modules/Locality/Epimorphisms](../Modules/Locality/Epimorphisms.lean),
[Modules/Flat/Relative/LocalOnTarget](../Modules/Flat/Relative/LocalOnTarget.lean),
[Modules/LocallyFree/EqualRank](../Modules/LocallyFree/EqualRank.lean),
[Properties/Noetherian/LocallyNoetherianOver](../Properties/Noetherian/LocallyNoetherianOver.lean),
[Grassmannian/Quotient/UniversalQuotientPullback](../Grassmannian/Quotient/UniversalQuotientPullback.lean),
[CategoryTheory/Abelian/KernelCompEpi](../../CategoryTheory/Abelian/KernelCompEpi.lean),
[CategoryTheory/Monoidal/Untwist](../../CategoryTheory/Monoidal/Untwist.lean),
[CategoryTheory/Monoidal/UntwistVanishing](../../CategoryTheory/Monoidal/UntwistVanishing.lean)
and the Grassmannian leaves [Kernel](../../RingTheory/Grassmannian/Kernel.lean),
[MapCriterion](../../RingTheory/Grassmannian/MapCriterion.lean) and
[LinearEquiv](../../RingTheory/Grassmannian/LinearEquiv.lean).
The open step uses [Morphisms/UniversallyClosed/ImageComplement](../Morphisms/UniversallyClosed/ImageComplement.lean)
and [Sites/OverRepresentability/OpenSubscheme](../Sites/OverRepresentability/OpenSubscheme.lean).
The immersed Hilbert functor uses [IdealSheaf/Monomorphism](../IdealSheaf/Monomorphism.lean) and
[Limits/FibreProductBaseChange](../Limits/FibreProductBaseChange.lean).
The coproduct and nonemptiness leaves use [IdealSheaf/EmptySubscheme](../IdealSheaf/EmptySubscheme.lean),
[IdealSheaf/GlueDisjoint](../IdealSheaf/GlueDisjoint.lean),
[IdealSheaf/GlueCoproduct](../IdealSheaf/GlueCoproduct.lean),
[Limits/CoproductPullback](../Limits/CoproductPullback.lean),
[FlatteningStratification/FlatDecomposition](../FlatteningStratification/FlatDecomposition.lean) and
[Cohomology/Projective/HilbertPolynomial/ZeroModule](../Cohomology/Projective/HilbertPolynomial/ZeroModule.lean).

[QuasiProjective](QuasiProjective.lean): over a Noetherian ring the Hilbert scheme of `P^n_A` is
H-quasi-projective over `Spec A` (`ProjectiveSpace.isHQuasiProjective_hilbertSchemeOver_hom`), as a
locally closed subscheme of the H-projective Grassmannian; hence separated and of finite type.

**Fibres of an embedded family.** [Immersed/Fiber](Immersed/Fiber.lean): for `i : X ⟶ P^N_A`, `g : T
⟶ Spec A` and a field point `x : Spec K ⟶ T`, the fibre `X_x = X ×_{Spec A} Spec K` is the base
change of `i_T` along `pointMap ι g x`, by the cartesian square of `b_x : X_x ⟶ X_T`, the fibre
embedding `embeddedFiberι i (x ≫ g)`, `i_T` and `pointMap ι g x`; hence the fibre at `x` of the
image of a closed `V ⊆ X_T` is the image of the fibre `V_x`, its Hilbert polynomial is that of the
pushforward of `𝒪_{V_x}`, and for a closed immersion `i` its value at `n` is `χ(X_x, O(n)) − χ(X_x,
I_{V_x}(n))` (additivity on `0 → I_{V_x} → 𝒪_{X_x} → 𝒪_{V_x} → 0` pushed to `P^N_K`). For `V` flat
over `T`, `I_{V_x} ≅ b_x^* I_V` and the image is flat, and evaluations `ψ`, `φ₀` give the polynomial
`ψ − φ₀`. This is the computation behind Kleiman's "Plainly `Z` lies in `Hilb^θ_{X/S}(n)`"
(arXiv:math/0504020v1, p. 30); the [Picard strata](../Picard/Strata/DivisorPolynomial.lean) consume
it.

[Divisor](Divisor/Functor.lean): for a closed immersion `i : X ⟶ P^n_A` over `Spec A` with `X` flat
over `A`, the functor `Div^θ_X` (`relativeDivisorFunctor i hi θ`, X-first: relative effective
Cartier divisors `D ⊆ X ×_{Spec A} T` over `T` whose images in `P^n_A ×_{Spec A} T` have fibre
Hilbert polynomial `θ`; Kleiman, arXiv:math/0504020v1, Def. 3.6, p. 23) is an open subfunctor of the
Hilbert functor of `X` on locally Noetherian test schemes
(`isOpenSubfunctor_locallyNoetherianRelativeDivisorSubfunctor`), and for any representation `E` of
the latter by `H` it is represented by the open subscheme `divisorSchemeOver E` of `H`
(`fiberCartierLocus` of the universal family), with universal divisor `universalDivisor E` (Kleiman,
Thm 3.7, statement p. 23, proof p. 24). Over a Noetherian `A`, the closed Hilbert scheme of `i.ker`
represents the Hilbert functor of `X`
(`locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion`,
[Immersed/ClosedImmersion](Immersed/ClosedImmersion.lean)), so `Div^θ_X` is represented by an
H-quasi-projective Noetherian scheme
(`exists_locallyNoetherianRelativeDivisorFunctor_representableBy`). On the Picard strata the fibre
hypothesis of `IsRelativeDivisorFamily.of_isRelativeEffectiveCartier` is
`RelativePicard.subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_hasFiberDualEulerPolynomial`
([Picard/Strata/DivisorPolynomial](../Picard/Strata/DivisorPolynomial.lean)).

## Open toward Nitsure, §§5–6, for `P^n_A`

The following are not formalized. The list is an inventory, not a proof.

- **Projectivity of `G_Φ`** (Nitsure's valuative-criterion step, §5, p. 27), which would make
  the Hilbert scheme projective over `Spec A`; optional for representability.
- **The direct identification for an open `U ⊆ P^N_A`**:
  `immersedHilbertSubfunctor U.ι rfl Φ = openHilbertSubfunctor ι Φ U`. It is not needed: the
  open, closed and locally closed steps of Theorem 6.1 are `HilbertScheme/OpenSubscheme`,
  `HilbertScheme/ClosedSubscheme` and `HilbertScheme/Immersed/*`.
