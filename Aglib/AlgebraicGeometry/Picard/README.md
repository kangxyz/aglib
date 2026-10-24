# Picard functors over a base

The owner is `AlgebraicGeometry.Scheme.RelativePicard`. For a morphism of schemes
`p : X ⟶ S` the family constructs presheaves of additive commutative groups on
`Over S`, with values in `AddCommGrpCat.{u + 1}` for `S X : Scheme.{u}`. Every value
is an actual `Scheme.Modules.Invertible.PicardGroup`, and every map is the proved
additive pullback `Scheme.Modules.Invertible.PullbackTensor.Local.pullbackHom`; no
tensor-pullback or other theorem-family parameter is used. The functors are defined on
all of `Over S`, nonreduced and non-Noetherian test schemes included. The plan in
[PICARD_PLAN.md](../../../docs/PICARD_PLAN.md) restricts later representability
statements, not these definitions.

[Presheaf](Presheaf.lean), imported as `Aglib.AlgebraicGeometry.Picard.Presheaf`,
has no hypothesis on `p`:

- `picardFunctor : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}` is `Y ↦ Pic(Y)`;
- `familyScheme p : Over S ⥤ Scheme.{u}` is `T ↦ pullback p T.hom`, with Mathlib's
  `pullback.map p T.hom p T'.hom (𝟙 X) f.left (𝟙 S)` as transition maps;
  `familyProjection p` is the natural `pullback.snd`;
- `basePicardFunctor S := (Over.forget S).op ⋙ picardFunctor` is `T ↦ Pic(T)`, and
  `familyPicardFunctor p := (familyScheme p).op ⋙ picardFunctor` is
  `T ↦ Pic(X ×_S T)`, Kleiman's absolute functor `Pic_X` (Kleiman, arXiv:math/0504020v1,
  Def. 2.1, p. 16);
- `basePullback p : basePicardFunctor S ⟶ familyPicardFunctor p` is pullback along
  `pullback.snd`;
- `relativePicardFunctor p` is `P_{X/S}(T) = Pic(X ×_S T) / Pic(T)` (Kleiman, Def. 2.2,
  p. 17), the pointwise quotient by `baseImage p T`, the range of the base pullback, with
  transition maps `QuotientAddGroup.map`; `quotientProjection p` is the natural quotient
  map, surjective with kernel `baseImage p T` (`quotientProjection_app_ker`).

[Normalized](Normalized.lean), imported as `Aglib.AlgebraicGeometry.Picard.Normalized`,
assumes a section `o : S ⟶ X` with `ho : o ≫ p = 𝟙 S`, and nothing else:

- `originSection p o ho T = pullback.lift (T.hom ≫ o) (𝟙 T.left) _ : T.left ⟶ pullback p T.hom`,
  natural as `originSectionNatTrans`, with `originSectionNatTrans_familyProjection`;
- `originRestriction p o ho : familyPicardFunctor p ⟶ basePicardFunctor S` is pullback along
  the origin sections; `basePullback_originRestriction` proves that it retracts the base
  pullback, so `basePullback_app_injective` holds;
- `normalizedPicardFunctor p o ho` is the pointwise kernel `T ↦ ker(o_T^*)`
  (`normalizedSubgroup`), with `normalizedInclusion`;
- `quotientNormalizedIso p o ho : relativePicardFunctor p ≅ normalizedPicardFunctor p o ho`
  sends `[L]` to `L - pr₂^*(o_T^* L)`; `quotientNormalizedIso_inv` identifies its inverse
  with `normalizedInclusion ≫ quotientProjection`. The additive splitting lemma is
  `RelativePicard.Split.quotientEquiv`.

[Fppf](Fppf.lean), imported as `Aglib.AlgebraicGeometry.Picard.Fppf`, has no hypothesis
on `p`. `fppfPicardSheaf p` is `Pic_{X/S,(fppf)}`, Mathlib's
`(presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
(relativePicardFunctor p)`, with the plus-plus instance from
`Mathlib.CategoryTheory.Sites.LeftExact`. `toFppfPicardSheaf p` is the sheafification
unit `toSheafify`, and `fppfPicardSheafHomEquiv` with `fppfPicardSheafHomEquiv_apply`
records the universal property for fppf sheaves of abelian groups. For a class
`a : PicardGroup T`, `vanishingSieve a` is the sieve of morphisms `f` with
`pullbackClass f a = 0`. Every class vanishes on a Zariski covering by trivializing opens
(`vanishingSieve_mem_zariskiTopology`), hence on an fppf covering
(`vanishingSieve_mem_fppfTopology`). So the instances
`quotientProjection_isLocallyInjective` and `quotientProjection_isLocallySurjective` hold
for `Scheme.fppfTopology.over S`, `isIso_presheafToSheaf_map_quotientProjection` makes the
sheafified quotient map invertible, and `fppfFamilyPicardSheafIso p` identifies the fppf
sheafification of `familyPicardFunctor p` with `fppfPicardSheaf p`; its forward map is the
sheafification of `quotientProjection p` (`fppfFamilyPicardSheafIso_hom`)
(Kleiman, Def. 2.2, p. 17, and the remark after it).
[Stacks 0B9L](https://stacks.math.columbia.edu/tag/0B9L) defines the Picard functor as the
set-valued fppf sheafification of `T ↦ Pic(X_T)`; here sheafification is taken in
`AddCommGrpCat.{u + 1}`. The local-bijectivity criterion is Mathlib's
`GrothendieckTopology.WEqualsLocallyBijective` instance for `AddCommGrpCat.{u + 1}`.

[FppfSections](FppfSections.lean), imported as `Aglib.AlgebraicGeometry.Picard.FppfSections`, has
no hypothesis on `p`: the sheafification unit `toFppfPicardSheaf p` is locally injective and
locally surjective for `Scheme.fppfTopology.over S` (instances
`toFppfPicardSheaf_isLocallyInjective`, `toFppfPicardSheaf_isLocallySurjective`, from Mathlib's
`Presheaf.isLocallyInjective_toSheafify'` and `Presheaf.isLocallySurjective_toSheafify'`), and the
underlying presheaf of sets `(fppfPicardSheaf p).obj ⋙ forget AddCommGrpCat` is an fppf sheaf
(`isSheaf_fppfPicardSheaf_forget`).

[FiberCondition/Subsheaf](FiberCondition/Subsheaf.lean) and
[FiberCondition/OpenSubfunctor](FiberCondition/OpenSubfunctor.lean) give the generic
open-subsheaf lemma of Kleiman's proof of Thm 4.8 (arXiv:math/0504020v1, pp. 28–29), with fppf
coverings in place of étale ones. No hypothesis on `p : X ⟶ S` or on `S` is used.

- `FiberCondition p`: a condition `Holds T a t` on a point `t` of an `S`-scheme `T` and a class
  `a ∈ Pic(X ×_S T)`, with `holds_map` (for `g : T' ⟶ T` over `S`, the condition holds at `t'`
  for `g^* a` iff it holds at `g t'` for `a`; Kleiman p. 28, "remains valid after any base
  change") and `isOpen_setOf_holds` (open in locally Noetherian families). Classes make it
  invariant under isomorphism; `ofLineBundle` builds one from an isomorphism-invariant condition
  on line bundles. `holds_iff_holds_residuePoint` (only the fiber over `Spec κ(t)` matters),
  `holds_iff_of_eq` (classes with the same image in `Pic_{X/S,(fppf)}(T)` satisfy the condition at
  the same points), `holds_add_basePullback_iff` (invariance under `⊗` with classes from `T`).
  The conjunction `C ⊓ D` (`Min` instance) has `inf_holds`, `inf_holdsAt`, `subfunctor_inf` and
  `opens_inf`.
- For a section `ξ` of `Pic_{X/S,(fppf)}` over `T`: `HoldsAt ξ t` (some local representative
  satisfies the condition at a point over `t`), `exists_flat_app_eq` (a representative along an fppf
  morphism through every point), `holdsAt_iff` (independent of the representative), `holdsAt_map`
  (base change).
- `C.subfunctor = Pic^C`: Mathlib's `Subfunctor.sheafify` for `Scheme.fppfTopology.over S` of the
  image presheaf `C.imageSubfunctor` (Kleiman's "subsheaf associated to the presheaf" of classes
  satisfying the condition everywhere), defined on all of `Over S`; `isSheaf_subfunctor`,
  `mem_subfunctor_iff` (sections satisfying the condition at every point), `app_mem_subfunctor_iff`.
- For `T` locally Noetherian: `isOpen_setOf_holdsAt`, the open `C.opens ξ` (Kleiman's `T^φ`),
  `map_mem_subfunctor_iff` (for every `g : Z ⟶ T` over `S`, `Z` arbitrary, `g^* ξ ∈ Pic^C` iff
  `g.left ⁻¹ᵁ C.opens ξ = ⊤`), `mem_subfunctor_iff_opens_eq_top`; if the failure of the condition
  is also open (an `IsClosed` hypothesis), `isClosed_setOf_holdsAt_of_isClosed` and
  `isClopen_setOf_holdsAt_of_isClosed`.
- Consumer form on `Scheme.LocallyNoetherianOver S`: `C.locallyNoetherianSubfunctor`
  (`LocalRepresentability.restrictSubfunctor`), `isOpenSubfunctor`
  (`LocalRepresentability.IsOpenSubfunctor`, the openness field of `SubfunctorCover`; Stacks, Tag
  01JI), `preimageSubfunctor ξ` (`Pic^C ×_{Pic} h_T` inside the functor of points of `T`),
  `preimageRepresentableBy` (represented by `LocalRepresentability.restrictOpens T (C.opens ξ)`,
  through `restrictOpensι`; `preimageRepresentableBy_homEquiv_coe`).
- Families: `opens_mono`, `disjoint_opens`, `iSup_opens_eq_top` (Kleiman p. 29: the `T^φ` are
  disjoint and cover `T`; the `P^φ_m ×_{P^φ} T` are nested with union `T`).

Kleiman descends the open locus of a representative along the étale covering; here the open is
the intrinsic locus `{t | HoldsAt ξ t}`, whose preimage under each fppf morphism with a
representative is the open locus of the representative, and fppf morphisms are open maps. The
locally Noetherian hypothesis on `T` enters only through the openness field, applied to the
fppf `V ⟶ T`, which are locally of finite type. The focused tests are
`AglibTest.AlgebraicGeometry.Picard.FiberCondition.Subsheaf` and `.OpenSubfunctor` (with axiom
guards). Planned consumers: the strata `Pic^φ = C_φ.subfunctor` and
`Pic^φ_m = (C_φ ⊓ C_m).subfunctor` (F17 step 2), where `C_m` is the single condition
"`H^i(X_t, L_t(n)) = 0` for `i ≥ 1`, `n ≥ m`, and `H^0(X_t, L_t(m)) ≠ 0`"; the nonvanishing
condition is open only inside the vanishing locus, so it is not a fiber condition by itself. A
further consumer is `Z := Pic^{φ₀}_0 ×_{Pic} Div` open in `Div` (F17 step 3,
`preimageRepresentableBy` at `T = Div^θ`).

[Comparison](Comparison/README.md) adds the rigidified functor with Kleiman's Lemmas
2.9 and 2.10. It also reduces the injectivity of `toFppfPicardSheaf` (Thm 2.5(1)) to the
equivalent premise `FppfLocallyTrivialMemBaseImage`.

Not yet proved here:

- that premise under universal O-connectedness;
- the bijectivity of `toFppfPicardSheaf` with a section (target 4 of the plan);
- representability.

Source provenance: `R5Lab.AlgebraicGeometry.Curves.RelativePicard` and
`RelativePicard/Group.lean`. Retained names: `basePicardFunctor`, `familyPicardFunctor`,
`basePullback`, `originSection`, `originRestriction`, `basePullback_originRestriction`,
`normalizedInclusion`, `quotientNormalizedEquiv`, `quotientNormalizedIso`,
`quotientProjection` and `Split`; `basePullback_injective` is now
`basePullback_app_injective`.
The R5Lab `Type (u + 1)`-valued `basePicardFunctor`, `familyPicardFunctor` and
`normalizedClassFunctor` are the composites of the presheaves here with
`forget AddCommGrpCat`, with definitionally equal values on objects. Their transition
maps agree only propositionally: R5Lab's `familyMap` is `pullback.lift fst (snd ≫ a)`,
whereas `familyScheme` uses `pullback.map`, so retargeting R5Lab needs an explicit
comparison of maps. R5Lab's
`basePicardGroupFunctor`, `familyPicardGroupFunctor`, `normalizedGroupFunctor` and
`relativeQuotientGroupFunctor` correspond to `basePicardFunctor`, `familyPicardFunctor`,
`normalizedPicardFunctor` and `relativePicardFunctor`. The R5Lab relative quotient used
the section to define its transition maps; here they are induced by the base pullback
and need no section. R5Lab's `RelativeDivisors.familyMap` is replaced by
`pullback.map`, and its `ModuleTensorPullback` parameter by the proved `pullbackHom`.

Lower prerequisites are the [Invertible](../Modules/Invertible/README.md) family
(`PicardGroup`, `pullbackClass`, `PullbackTensor.Local.pullbackHom`), Mathlib's
`pullback.map`, `Scheme.fppfTopology`, `GrothendieckTopology.over` and sheafification.
The present consumer is the focused test `AglibTest.AlgebraicGeometry.Picard.Functors`;
`AglibTest.AlgebraicGeometry.Picard.Interfaces` records the M0 interface probes.
Planned consumers are the comparison and rigidification layer (plan F7), the
representability assembly (F17) and the R5Lab `Curves.RelativePicard` retargeting.

The [Relative compatibility guide](Relative/README.md) identifies the incoming
class/group functors and their actual transition maps with the native Picard
presheaves. Original schemes and test schemes may be arbitrary, including
nonreduced and non-Noetherian tests. The proper-flat sheaf comparison separately
keeps its locally Noetherian original base and geometrically integral fibres.
The [curve representability interface](../Curves/RelativePicard/Representability.lean)
remains an input to the prescribed-origin genus-one construction.
[PowerRoot](PowerRoot.lean), [PowerDescent](PowerDescent.lean) and
[FrameTorsor](FrameTorsor.lean) describe actual root, descent and frame objects.

[Tangent/Thickening](Tangent/Thickening.lean), [Tangent/Generator](Tangent/Generator.lean) and
[Tangent/DualNumbers](Tangent/DualNumbers.lean) give the algebraic core of the tangent space
of the Picard functor (Kleiman, arXiv:math/0504020v1, proof of Thm 5.11, p. 43). For morphisms
`i : X ⟶ Y` and `p : Y ⟶ X` with `i ≫ p = 𝟙 X`, `SplitThickening.ringSheaf p` is `p_* 𝒪_Y` on
the Zariski site of `X`, with the closed-fibre map `reduction i p h` and its section
`projectionMap p`. Given square-zero section kernels (`reduction_ker_sq` from quasi-compact
`i` with `i.ker ^ 2 = ⊥`, or `IdealGenerator.reduction_ker_sq`), the original unit sequence is
short exact and split, and `unitsCohomologyEquiv` gives
`H^n((p_* 𝒪_Y)^*) ≃+ H^n(I) × H^n(𝒪_X^*)` in every degree. `picardRetractionEquiv` splits
`Pic(Y) ≃+ Pic(X) × ker(i^*)` with no further hypothesis. An `IdealGenerator` `ε` identifies the
additive kernel `I` with `𝒪_X` (`IdealGenerator.kernelIso`), so the truncated exponential
sequence `0 → 𝒪_X → (p_* 𝒪_Y)^* → 𝒪_X^* → 1`, `b ↦ 1 + bε`, is short exact and split. For
`X[ε] = X ×_{Spec k} Spec k[ε]` over any commutative ring `k`,
`DualNumbers.dualIdealGenerator` supplies `ε`; on an affine open `W`, sections over `p⁻¹ W`
are the pushout `Γ(X, W) ⊗ k[ε]` (Mathlib `isIso_pushoutSection_of_isAffineOpen`). The
identification `ker(i^*) ≃+ H^1(X, 𝒪_X)` (`picardKerEquiv`, `picardEquiv`) takes the premise
`UnitsCohomologyComparison`: Zariski `Pic = H^1(𝒪^*)` for `Y` on the common space (an
equivalence) and for `X` (an injective map) (Stacks, Tag 09NU, `lemma-h1-invertible`, for the
isomorphisms; compatibility with `i^*` is a separate naturality statement). Kleiman uses this
identification tacitly in the sentence before Square (5.11.4); the square itself, which
compares `H^1(𝒪^*_{X_T})` with `Pic_{X/k}(T)`, and (5.11.3) are not formalized. Aglib proves
only the étale form `FrameTensor.picardH1Equiv`. No separatedness, quasi-compactness or
Noetherian hypothesis on `X` is used. The focused test is
`AglibTest.AlgebraicGeometry.Picard.Tangent`.
