# The Hilbert functor of projective space and its Grassmannian embedding

This family formalizes the Hilbert functor `Hilb^Φ` of `P^n_A = ProjectiveSpace A ι` and its
embedding into a Grassmannian, following Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1: §1, pp. 2–4 (the functor), §5, pp. 24–26 ("Use of m-Regularity",
"Embedding Quot into Grassmannian", "Use of Flattening Stratification", property (F)). Throughout,
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
[RingTheory/Spectrum/Prime/FreeLocus/ResidueField](../../RingTheory/Spectrum/Prime/FreeLocus/ResidueField.lean)
and the Grassmannian leaves [Kernel](../../RingTheory/Grassmannian/Kernel.lean),
[MapCriterion](../../RingTheory/Grassmannian/MapCriterion.lean) and
[LinearEquiv](../../RingTheory/Grassmannian/LinearEquiv.lean).

## Open toward Nitsure, Theorem 5.1 for `P^n_A`

The following are not formalized. The list is an inventory, not a proof.

- **Locally Noetherian test schemes.** The points are natural only on Noetherian affine test
  schemes. Extending them to locally Noetherian `T` needs:
  - a Noetherian variant of the Grassmannian gluing: the overlap agreement of
    `Grassmannian.localFunctor` quantifies over all `A`-algebras, so the descent must be arranged
    so that only locally Noetherian schemes occur, for example through the chart intersections;
  - the test category itself: a full subcategory of locally Noetherian schemes over `Spec A`,
    with the restrictions of `hilbertFunctor` and `quotFunctor` to it;
  - the glued element of `quotFunctor` from the values of `noetherianAffineGrassmannianNatTransFin`
    on Noetherian affine opens. The naturality proved here is an equality of submodules, so the
    overlap isomorphisms are canonical; a sheaf-level `π_* 𝒪_Z(r)` is not required.
- **The universal subscheme.** `Z_univ = V(Im(π^*K(-r) → 𝒪))` on `P^n_A ×_A Gr` as an ideal
  sheaf: the epimorphism onto the image ideal of `Hom.imageIdealData` is not yet proved.
- **The Grassmannian side** is available in the [Grassmannian family](../Grassmannian/README.md):
  the universal quotient (`Grassmannian.universalQuotient`), its kernel `K`
  (`Grassmannian.universalKernel`, included into the free sheaf on the monomials through `ofFree`
  and `pullbackUniversalKernelIsoOfFree_hom_ι`), and `IsNoetherian` over a Noetherian base
  (`Grassmannian/Finiteness`). The transport `A[x]_r ≅ A^N` is
  `noetherianAffineGrassmannianNatTransFin`.
- **The two inclusions.** "⇒": `Z = Z_univ.comap φ_Z`, from the image description of the ideal of
  a pulled-back closed subscheme and global generation of `I_Z(r)`. "⇐": `g^*K = π_* I_{Z_T}(r)`,
  two subbundles of equal rank with locally free quotients.
- **Bookkeeping** of the structure maps `g ≫ s` against `t`, through `IsHilbertFamily.comap` with
  `f = 𝟙`.
