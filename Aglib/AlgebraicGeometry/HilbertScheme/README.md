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

[QuasiProjective](QuasiProjective.lean): over a Noetherian ring the Hilbert scheme of `P^n_A` is
H-quasi-projective over `Spec A` (`ProjectiveSpace.isHQuasiProjective_hilbertSchemeOver_hom`), as a
locally closed subscheme of the H-projective Grassmannian; hence separated and of finite type.

## Open toward Nitsure, §§5–6, for `P^n_A`

The following are not formalized. The list is an inventory, not a proof.

- **Projectivity of `G_Φ`** (Nitsure's valuative-criterion step, §5, p. 27), which would make
  the Hilbert scheme projective over `Spec A`; optional for representability.
- **The remaining subfunctors of Theorem 6.1** (§6): the open step for an open `U ⊆ P^N_A` is
  `HilbertScheme/OpenSubscheme` (with `Hilb^Φ_U` the subfunctor of families contained in `U`).
  Open: the identification of `Hilb^Φ_U` with the Hilbert functor of `U` itself (a closed
  subscheme of `U_T`, proper over `T`, is closed in `P^N_T`; Exercise B, p. 28), the closed step
  for `C ⊆ P^N_A`, the locally closed combination, and quasi-projectivity.
