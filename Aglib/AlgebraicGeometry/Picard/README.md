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

[GroupLaw](GroupLaw.lean), imported as `Aglib.AlgebraicGeometry.Picard.GroupLaw`: for `S` locally
Noetherian, any `p`, and a representation `e` of `Pic_{X/S,(fppf)}` on locally Noetherian test
schemes by `P` locally of finite type over `S` (an explicit argument; its existence is target 5),
`picardCommGrpObj p P e` is a commutative group object structure on `P` in `Over S`, and `e` turns
the group law of `T ⟶ P` into the addition of `Pic_{X/S,(fppf)}(T)` (`picard_homEquiv_one`,
`picard_homEquiv_mul`, `picard_homEquiv_inv`, `picardHomAddEquiv`). Consumer:
[IdentityComponent](IdentityComponent.lean).

[IdentityComponent](IdentityComponent.lean), imported as
`Aglib.AlgebraicGeometry.Picard.IdentityComponent`: for a field `k`, `p : X ⟶ Spec k` and a
representation `e` of `Pic_{X/k,(fppf)}` on locally Noetherian test schemes by `P` locally of finite
type over `k` (an explicit argument), `picardIdentityComponent p P e` is the identity component of
`P` for the group law `picardCommGrpObj p P e`, with inclusion `picardIdentityComponentι p P e`. It
is open and closed (`isClopen_picardIdentityComponent`; inclusion an open immersion), a group
subscheme (`grpObjPicardIdentityComponent`, `isMonHom_picardIdentityComponentι`), of finite type
(`quasiCompact_picardIdentityComponent_hom`, `locallyOfFiniteType_picardIdentityComponent_hom`,
`quasiCompact_and_locallyOfFiniteType_picardIdentityComponent`), geometrically irreducible
(`geometricallyIrreducible_picardIdentityComponent_hom`), and the identity component of the base
change `P_K` is the preimage of `Pic⁰` (`picardIdentityComponent_pullback`,
`pullbackPicardIdentityComponentIso`): Kleiman, Prop. 5.3, p. 37, without the separatedness and
smoothness clauses. The base change `P_K` carries the base-changed group law; that it represents
`Pic_{X_K/K,(fppf)}` (Kleiman Ex. 4.4) is not used.

[FamilyBaseChange](FamilyBaseChange.lean), imported as
`Aglib.AlgebraicGeometry.Picard.FamilyBaseChange`, has no hypothesis: for `g : S' ⟶ S` and
`p' := pullback.snd p g`, `familyBaseChangeIso p g T : (X ×_S S') ×_{S'} T ≅ X ×_S T` (Mathlib's
`pullbackLeftPullbackSndIso`, typed between the literal fibre products),
`familySchemeBaseChangeIso p g : familyScheme p' ≅ Over.map g ⋙ familyScheme p`,
`familyPicardFunctorBaseChangeIso p g : familyPicardFunctor p' ≅ (Over.map g).op ⋙ familyPicardFunctor p`,
and the compatibility with the base pullbacks
`basePullback_comp_familyPicardFunctorBaseChangeIso_hom` (Kleiman, Ex. 4.4, p. 27, Answer 4.4, p.
65, presheaf level). Consumer: the fppf base change [BaseChange](BaseChange.lean).

[BaseChange](BaseChange.lean), imported as `Aglib.AlgebraicGeometry.Picard.BaseChange`, has no
hypothesis: for `g : S' ⟶ S` and `p' := pullback.snd p g`,
`fppfPicardSheafBaseChangeIso p g : (fppfPicardSheaf p').obj ≅ (Over.map g).op ⋙ (fppfPicardSheaf p).obj`
(`Pic_{X'/S',(fppf)}(T) ≅ Pic_{X/S,(fppf)}(T)` naturally in the `S'`-scheme `T`), the same
isomorphism of fppf sheaves `fppfPicardSheafBaseChangeSheafIso p g` with target Mathlib's
`Functor.sheafPushforwardContinuous` along `Over.map g`, and the base change of the relative Picard
functors `relativePicardFunctorBaseChangeIso p g`, induced by `familyPicardFunctorBaseChangeIso`.
The sheafified step is Mathlib's `Functor.pushforwardContinuousSheafificationCompatibility` (the
pointwise Kan-extension and both `HasWeakSheafify` instances are found by instance search for
`AddCommGrpCat.{u + 1}`), between the identifications `fppfFamilyPicardSheafIso` for `p` and `p'`;
the continuity and cocontinuity it needs are the correspondence of coverings, recorded as
`fppf_functorPushforward_over_map_mem_iff` (a family of `S'`-schemes covers if and only if it covers
over `S`; the reason Kleiman gives, in Answer 4.4, p. 65, for the identification that "holds
essentially by definition"). Compatibility with the units:
`toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom` (relative functors),
`quotientProjection_comp_toFppfPicardSheaf_comp_fppfPicardSheafBaseChangeIso_hom` (family functors)
and, on the class of a line bundle, `fppfPicardSheafBaseChangeIso_hom_app_toFppfPicardSheaf_mk`.
Naturality: `fppfPicardSheafBaseChangeIso_hom_naturality` and
`fppfPicardSheafBaseChangeIso_hom_app_map_apply`. For `i : T₀ ⟶ T` over `S'`,
`fppfPicardSheafBaseChangeKerAddEquiv p g i` identifies the kernels of the restrictions along `i`
and along `(Over.map g).map i` (`fppfPicardSheafBaseChangeKerAddEquiv_apply_coe`). Kleiman, Ex. 4.4,
p. 27, Answer 4.4, p. 65. Consumer: the tangent-space comparison of target 6 at `Spec K[ε]` and
`Spec K`.

[BaseChangeRepresentableBy](BaseChangeRepresentableBy.lean), imported as
`Aglib.AlgebraicGeometry.Picard.BaseChangeRepresentableBy`: for `S'` locally Noetherian, any `p`,
and a representation `e` of `Pic_{X/S,(fppf)}` on locally Noetherian test schemes by `P` locally of
finite type over `S` (an explicit argument; no hypothesis on `S`),
`baseChangeRepresentableBy p g P e` represents `Pic_{X'/S',(fppf)}` on locally Noetherian
`S'`-schemes by `LocallyNoetherianOver.baseChange g P`, the object `(Over.pullback g).obj P.obj`
(`P ×_S S'`;
[Properties/Noetherian/LocallyNoetherianOverBaseChange](../Properties/Noetherian/LocallyNoetherianOverBaseChange.lean)).
Its bijection (`baseChangeRepresentableBy_homEquiv`) is Mathlib's `Over.mapPullbackAdj g`, then `e`
at the `S`-scheme `T` (`LocallyNoetherianOver.map g`, which keeps the scheme), then the inverse of
`fppfPicardSheafBaseChangeIso p g`. Built from the generic
`ObjectProperty.representableByLiftOfAdjunction`. Kleiman, Ex. 4.4, p. 27, Answer 4.4, p. 65.
Consumer: the instantiation of target 6.

[BaseChangeGroupLaw](BaseChangeGroupLaw.lean), imported as
`Aglib.AlgebraicGeometry.Picard.BaseChangeGroupLaw`: for `S` and `S'` locally Noetherian, the group
law of `P ×_S S'` as the scheme representing `Pic_{X'/S',(fppf)}` (`picardCommGrpObj` for
`baseChangeRepresentableBy p g P e`) is the base change of the group law of `P`, Mathlib's
`Functor.grpObjObj` for `Over.pullback g`, i.e. the group law of `(Over.pullback g).mapGrp` and of
`groupSchemeBaseChange g` (`picardCommGrpObj_baseChange_toGrpObj`). The base-changed law makes the
representation additive (`baseChangeRepresentableBy_homEquiv_mul`), by the multiplicativity of the
adjunction bijection (`Adjunction.homEquiv_symm_mul`); the two laws agree at the test scheme
`(P ×_S S') ×_{S'} (P ×_S S')`, locally of finite type over `S'`.

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
- representability on all test schemes, beyond locally Noetherian ones (Noetherian approximation
  of line bundles; deferred in [PICARD_PLAN.md](../../../docs/PICARD_PLAN.md)).

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
identification tacitly in the sentence before Square (5.11.4); the square in its `Pic` form,
with the fppf Picard sheaf, is `Tangent/Comparison`; (5.11.3) is not formalized here. Aglib proves
only the étale form `FrameTensor.picardH1Equiv`. No separatedness, quasi-compactness or
Noetherian hypothesis on `X` is used. The focused test is
`AglibTest.AlgebraicGeometry.Picard.Tangent`.

[Tangent/Cech](Tangent/Cech/DualNumbers.lean) computes the kernel of `i^* : Pic(Y) → Pic(X)` by Čech
cocycles, without the premise `UnitsCohomologyComparison`. For a split thickening with an
`IdealGenerator` (`Tangent/Cech/Units`: the units `1 + ε p^♯ b`, and on affine opens the units with
reduction 1 are exactly these), a pair cocycle `b` on a cover `U` of `X` gives the unit cocycle
`1 + ε b` on `p⁻¹ U` and the class `cocycleClass U hU b` (`Tangent/Cech/Cocycle`), an additive map
into `ker i^*` whose kernel is the pair coboundaries when the `U j` are affine.
`Tangent/Cech/Frames` shows every class in `ker i^*` arises, when `U j`, `p⁻¹ U j` and `U j ⊓ U l`
are affine: frames on `p⁻¹ U j` come from `exists_lineBundle_iso_lift_affine_of_square_zero`, and
the frame cocycle is normalized to reduction 1 through `UnitCocycle.pullbackIso` along `i`.
`Tangent/Cech/Equiv` gives `IdealGenerator.pairCohomologyEquivKer : PairCohomology U ≃+ ker i^*`.
For the dual numbers (`Tangent/Cech/DualNumbers`), let `k` be any commutative ring, `X` a scheme
over `Spec k`, and `U` a cover (`iSup U = ⊤`) by affine opens with affine pairwise intersections.
Then `picardKerEquivPairCohomology : ker(Pic X[ε] → Pic X) ≃+ PairCohomology U`. The preimages
`p⁻¹ U j` are affine because `X[ε] ⟶ X` is affine (`isAffineHom_projection`). Now let `k` be a
field, `X : FScheme k` with `X.left` separated, and `U` a cover (`iSup U = ⊤`) by affine opens. Then
`picardKerEquivCech : ker(Pic X[ε] → Pic X) ≃+ structureCohomology k X 1` composes it with
`Cohomology.pairCohomologyEquivCech` and `Cohomology.structureCechCohomologyLinearEquiv`. It has the
type of the conditional `DualNumbers.picardKerEquiv`, and `picardKerEquivCech_cocycleClass` gives
its value on glued classes. `Tangent/Cech/Scaling` defines `dualScale a : X[ε] ⟶ X[ε]` from
`µ_a : ε ↦ aε` and proves `picardKerEquivCech_dualScale`: pulling back along `dualScale a` is
multiplication by `a` (Kleiman, arXiv:math/0504020v1, proof of Thm 5.11, pp. 42–43). The cover need
not be finite. The focused test is `AglibTest.AlgebraicGeometry.Picard.Tangent.Cech`.

[Tangent/Points](Tangent/Points.lean) computes the tangent space at the unit of a functor
`F : (Over (Spec k))ᵒᵖ ⥤ AddCommGrpCat` whose restriction to locally Noetherian test schemes is
represented by `P` (Kleiman, arXiv:math/0504020v1, proof of Thm 5.11, (5.11.1)–(5.11.3), pp. 42–43).
The representation `e` is an explicit argument; no group scheme and no finite-type hypothesis on `P`
is used. `unitSection e : Spec k ⟶ P` represents `0 ∈ F(k)`; `unitStalk e = 𝒪_{P,x₀}` is a
`k`-algebra through the structure map (`unitStalkAlgebra`), and `unitResidue e : 𝒪_{P,x₀} →ₐ[k] k`,
the stalk map of the unit section, makes `k` its residue field. For a field `L` over `k` and a
finite-dimensional `L`-module `M`, the kernel `squareZeroKernel F L M` of `F(L ⊕ M) → F(L)`
(`tangentKernel F L` for `L[ε] = L ⊕ L`) is `Hom_k(𝔪/𝔪², M)` (`squareZeroKernelEquiv`): through the
points reducing to the unit section (`squareZeroKernelEquivPoints`), the local `k`-algebra maps
reducing to the residue map (`squareZeroLiftEquivPoints`, from Mathlib's `SpecToEquivOfLocalRing`)
and the cotangent lifts (`IsLocalRing.trivSqZeroExtLiftEquiv`), see
`squareZeroKernelEquiv_eq_trans`; `squareZeroKernelEquivDerivation` is the derivation form. The
identification is natural for `L`-linear maps acting through `TrivSqZeroExt.map`
(`squareZeroKernelEquiv_map`). Hence it is additive (`squareZeroKernelAddEquiv`,
`tangentKernelEquiv`; a variant of Kleiman's argument, pp. 42–43, through `L ⊕ M²`) and `L`-linear
for `a • t = F(µ_a) t` (`tangentKernelEquiv_scale`, `tangentKernelModule`,
`tangentKernelLinearEquiv`). `finrank_tangentKernel` gives
`finrank_L ker(F(L[ε]) → F(L)) = finrank_k (𝔪/𝔪²)` for every field `L` over `k`, finite since `P` is
locally Noetherian (`finite_tangentKernel`); `finrank_squareZeroKernel` is the `L ⊕ M` form. The
focused test is `AglibTest.AlgebraicGeometry.Picard.Tangent.Points`.

[Tangent/Comparison](Tangent/Comparison.lean) gives the vertical maps of Kleiman's Square (5.11.4)
(arXiv:math/0504020v1, proof of Thm 5.11, pp. 43–44) for the fppf Picard sheaf. Let `k` be a field,
`X : FScheme k` with structure map `p`, and `F = (fppfPicardSheaf p).obj`. The closed point and
`µ_a : ε ↦ aε` are the morphisms
`DualNumbers.closedPointOver k : Over.mk (𝟙 (Spec k)) ⟶ Over.mk (dualMap k)` and
`DualNumbers.scaleOver k a` of `k`-schemes; on the fibres `X ×_k -` they induce `i` through
`pullback.fst : X ×_k Spec k ≅ X` (`familyClosedPoint_eq`) and `dualScale a` (`familyScale_eq`). The
vertical maps `toFppfDualNumbers X : Pic(X[ε]) →+ F(k[ε])` and
`toFppfClosedFibre X : Pic(X) →+ F(k)` are `quotientProjection` followed by `toFppfPicardSheaf`. The
square `F(ρ) ∘ toFppfDualNumbers X = toFppfClosedFibre X ∘ i^*` commutes by naturality of the unit
(`fppfPicardSheaf_map_closedPointOver_toFppfDualNumbers`), compatibly with `µ_a`
(`fppfPicardSheaf_map_scaleOver_toFppfDualNumbers`), and `picardKerToFppf X : ker(i^*) →+ ker F(ρ)`
is the induced map of kernels. For `p` proper and flat with geometrically integral fibres both
vertical maps are injective (Kleiman, Thm 2.5(1), p. 18, with `Pic(k) = Pic(k[ε]) = 0`;
`RelativePicard.quotientProjection_app_injective_of_subsingleton`). With `IsSplitEpi p` they are
bijective (Thm 2.5(2), p. 18), and
`fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X : ker F(ρ) ≃+ ker(i^*)` has
inverse `picardKerToFppf X` and carries `F(µ_a)` to `dualScaleKer a`. This replaces Kleiman's
Exercise 2.3 over an algebraically closed field by Thm 2.5(2) with a section, over any field.
[Tangent/KernelMap](Tangent/KernelMap.lean) defines Kleiman's `v` (proof of Thm 5.11, p. 43) for
`X.left` separated and a cover `U` by affine opens:
`cohomologyToFppfPicardKer X U hU hU₁ : H^1(X, 𝒪_X) →+ ker F(ρ)` is `picardKerEquivCech⁻¹` followed
by `picardKerToFppf X`; no section is used. It satisfies `v (a • c) = F(µ_a) (v c)`
(`cohomologyToFppfPicardKer_smul`), is injective for `p` proper and flat with geometrically integral
fibres, and with a section is the inverse comparison after `picardKerEquivCech⁻¹`, hence bijective
(`cohomologyToFppfPicardKer_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral`).
`scaleRingHom_eq_map` identifies `µ_a` with Mathlib's `TrivSqZeroExt.map (a • id)`. The focused
tests are `AglibTest.AlgebraicGeometry.Picard.Tangent.{Comparison,KernelMap}`.

[Tangent/FieldExtension](Tangent/FieldExtension.lean) compares, for any functor
`F : (Over (Spec k))ᵒᵖ ⥤ AddCommGrpCat`, the test objects of `Tangent/Points` with those of
`Tangent/Comparison`. Over `k`, `specOver k k[ε]` is `Over.mk (dualMap k)` by definition, while
`specOver k k` is `Over.mk (𝟙 (Spec k))` only up to `specOverSelfIso` (`Spec (algebraMap k k)` is
the identity through `Spec.map_id`); hence `tangentKernel F k = ker F(closedPointOver k)`
(`tangentKernel_eq_ker_closedPointOver`), `µ_a = scaleOver k a`
(`specOverMap_map_smul_id_eq_scaleOver`), and an additive map into `ker F(closedPointOver k)` linear
for `F(scaleOver k a)` is a `k`-linear map into `tangentKernel F k` for `tangentKernelModule e k`
(`linearMapToTangentKernel`). Over a field extension `K/k` with `g : Spec K ⟶ Spec k`,
`specOverDualNumberIso` and `specOverFieldIso` identify `specOver k K[ε]` and `specOver k K` with
`Spec K[ε]` and `Spec K` viewed through `Over.map g`, compatibly with the closed points and the
scalings; `kerClosedPointOverAddEquivTangentKernel` identifies
`ker F(Over.map g (closedPointOver K))` with `tangentKernel F K`, carrying
`F(Over.map g (scaleOver K a))` to `F(µ_a)` (`map_scaleOver_specOverDualNumberIso`). Given a functor
`G` on `K`-schemes and an equivalence of kernels compatible with the scalings,
`linearMapToTangentKernelOfFieldExtension` and `linearEquivTangentKernelOfFieldExtension` give the
`K`-linear map and, for bijective input, the `K`-linear equivalence. No hypothesis on `F`. The
focused test is `AglibTest.AlgebraicGeometry.Picard.Tangent.FieldExtension`.

[Tangent/StructureCohomology](Tangent/StructureCohomology.lean) proves Kleiman's Thm 5.11
(arXiv:math/0504020v1, p. 42) for the fppf Picard sheaf on locally Noetherian test schemes: let `k`
be a field, `X : FScheme k` proper and flat with geometrically integral fibres,
`F = Pic_{X/k,(fppf)}`, and `e` a representation of `F` on locally Noetherian test schemes by `P`
(an explicit argument). Then
`tangentKernelLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral X e` is a
`k`-linear equivalence `ker(F(k[ε]) → F(k)) ≃ₗ[k] H^1(X, 𝒪_X)` for `a • t = F(µ_a) t`, with inverse
Kleiman's `v` on the cover by all affine opens (its `_symm_apply`), and
`cotangentSpaceDualLinearEquivStructureCohomologyOfIsProperOfFlatOfGeometricallyIntegral X e` is the
Zariski form `(𝔪/𝔪²)^∨ ≃ₗ[k] H^1(X, 𝒪_X)`; also `finrank_k H^1(X, 𝒪_X) = finrank_k (𝔪/𝔪²)`, which is
finite
(`finrank_structureH1_eq_finrank_cotangentSpace_of_isProper_of_flat_of_geometricallyIntegral`). The
proof is a dimension count: `v` is injective and `k`-linear (`structureCohomologyToTangentKernel`,
`structureCohomologyToTangentKernel_injective_of_isProper_of_flat_of_geometricallyIntegral`; Thm
2.5(1), p. 18); for a residue field `K = κ(x)` the base change `X_K` has a section
(`Cohomology.exists_isSplitEpi_fieldBaseChange_hom`), so `ker(F(K[ε]) → F(K)) ≃ₗ[K] H^1(X_K, 𝒪)`
(`tangentKernelLinearEquivFieldBaseChangeOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral`,
through Thm 2.5(2), p. 18, the base change of the Picard sheaf, Ex. 4.4, p. 27, and Answer 4.4, p.
65, made compatible with `µ_a` by `fppfPicardSheafBaseChangeKerAddEquiv_map_scaleOver`, and
`Tangent/FieldExtension`); flat base change of `H^1` and `finrank_tangentKernel` at `K` and at `k`
give equal finite dimensions, so `v` is bijective
(`structureCohomologyToTangentKernel_bijective_of_isProper_of_flat_of_geometricallyIntegral`). This
replaces Kleiman's passage to an algebraically closed field (pp. 43–44, with Ex. 2.3). No group
scheme, finite-type or separatedness hypothesis on `P`, no rational point and no finiteness of
`κ(x)/k` is used. The focused test is
`AglibTest.AlgebraicGeometry.Picard.Tangent.StructureCohomology`.

[Strata/FiberConditions](Strata/FiberConditions.lean) defines, for a closed immersion
`i : X ⟶ P^N_A`, `s : T ⟶ Spec A`, a line bundle `L` on `X ×_{Spec A} T` and `t ∈ T`, the fibre
conditions of the strata of Kleiman's Thm 4.8 (arXiv:math/0504020v1, pp. 28–30) with the plan's
repairs: `HasFiberDualEulerPolynomial i s φ L t` (`χ(X_t, L_t^{-1}(n)) = φ(n)` for all `n`, (4.8.1)),
`HasFiberTwistVanishingAndSections i s m L t` (the single condition `C_m`: (4.8.3) for `n ≥ m` and
`h^0(X_t, L_t(m)) ≠ 0`), and `IsFiberStratum i s φ m L t = C_φ ∧ C_m`. They are invariant under
isomorphism and base change of the family (`hasFiberDualEulerPolynomial_pullback_iff`,
`hasFiberTwistVanishingAndSections_pullback_iff`), open (`C_φ` open and closed) on locally
Noetherian `T` for flat `f`, with each level `h^0(X_t, L_t(m)) = r` of the vanishing locus open
(`isOpen_setOf_hasFiberTwistVanishing_and_fiberTwistDim_zero_eq`), monotone in `m`, and cover
(geometrically integral fibres). The twist
`L ↦ L(m)` carries `C_φ ∧ C_m` to `C_{φ₀} ∧ C_0` with `φ₀(n) = φ(n - m)`
(`isFiberStratum_pulledTwistLineBundle_iff`); `fiberTwistClass` gives the classes `o_T(n)` with
`familyPicardFunctor_map_add_zsmul_fiberTwistClass`. The open-subsheaf bundling consumes these
pointwise statements.

The Picard strata use three layers: `Picard/FiberCondition/*` is the generic structure
`FiberCondition p` with its subsheaf, open-subfunctor, cover and translation lemmas;
`Picard/Strata/{FiberConditions,BaseAndRank}` state the pointwise fibre predicates `HasFiber…` of a
line bundle at a point; `Picard/Strata/{Conditions,Twist}` bundle them as `FiberCondition` values
(`Strata.eulerCondition`, …) and relate the strata by twisting.

[FiberCondition/RelativeCover](FiberCondition/RelativeCover.lean): if every point where a fiber
condition `C` holds satisfies some `D j`, the opens of the conjunctions `C ⊓ D j` cover the open of
`C` (`FiberCondition.iSup_opens_inf_eq`). [Strata/BaseAndRank](Strata/BaseAndRank.lean): the base
condition `HasFiberStructureEulerPolynomial i s ψ t` (`χ(X_t, O_{X_t}(n)) = ψ(n)`, through the
trivial line bundle, with no hypothesis on `A`: invariant under base change of the family and
determined by the image of `t` in `Spec A` for `f` proper; for a closed immersion `i` with
`ι ≃ Fin (N + 1)`, every point has a unique `ψ`, and for `f` also flat the locus is open and closed
on locally Noetherian `T`; over a Noetherian `A` only finitely many `ψ` occur,
`finite_setOf_exists_hasFiberStructureEulerPolynomial`), the level condition
`HasFiberTwistVanishingAndRank i s m r L t` ((4.8.3) for `n ≥ m` and `h^0(X_t, L_t(m)) = r`:
congruence, base change (`f` proper), the twist shift, openness on locally Noetherian `T` (closed
immersion, `f` flat), and, with geometrically integral fibres, some `r ≥ 1` at every `m ≫ 0`), and
the bridge to cohomology and base change at `m = 0`
(`HasFiberTwistVanishingAndRank.modulePointFiberCohomologyDimension_zero`: `h^0 = r`;
`HasFiberTwistVanishingAndRank.subsingleton_modulePointFiberCohomology`, for a closed immersion: the
higher point-fibre cohomology of `L` vanishes). [Strata/Conditions](Strata/Conditions.lean) bundles
the conditions, for a closed immersion `i` with `ι ≃ Fin (N + 1)` and `f` flat, as
`FiberCondition (i ≫ toSpec A ι)` values (`eulerCondition φ`, `baseCondition ψ`,
`levelCondition m r`, `coarseLevelCondition m`, `fineCondition φ ψ m r`, `coarseCondition φ m`),
whose subsheaves are the strata `Pic^φ`, `Pic^{φ,ψ,r}_m` and `Pic^φ_m`, and proves the covers of
Kleiman p. 29 with the plan's refinement, for sections over locally Noetherian `T`: the `C_φ`- and
`C_ψ`-opens are open and closed, disjoint and covering; the coarse strata increase with `m` and
exhaust `Pic^φ` (geometrically integral fibres); for fixed `(φ, m)` the fine strata with `r ≥ 1`
cover the coarse stratum; for fixed `m` the fine strata are pairwise disjoint; and, with
geometrically integral fibres, they cover `T` over the gluing index `(φ, ψ, m, k)`, `r = k + 1`. If
a representative `L` satisfies the fine condition at `m = 0` at every point of `T`, the geometric
fibres of `X_T ⟶ T` have `h^0(L) = r` and no higher cohomology of `L`
(`fibreCohomologyConcentrated_of_forall_fineCondition_holds`), and for `T` locally Noetherian
`p_* L` is locally free of rank `r` and every base-change map of `L` is an isomorphism
(`sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds`). `twistClass i m T`,
the class of `O_{X_T}(m)`, equals `m • twistClass i 1 T` (`twistClass_eq_zsmul`) and is natural in
`T`, and translation by `m • twistClass i 1 T` carries the fine condition at `(φ, ψ, m, r)` to the
one at `(φ₀, ψ, 0, r)`, `φ₀(n) = φ(n − m)` (`fineCondition_holds_add_twistClass`).

[FiberCondition/Translation](FiberCondition/Translation.lean): for a family of classes `c T ∈ Pic(X
×_S T)` compatible with pullback, translation `ξ ↦ ξ + γ_T` by the image `γ_T` of `c T` in
`Pic_{X/S,(fppf)}(T)` is a natural bijection with inverse `ξ ↦ ξ - γ_T` (`translationNatIso`); if
two fiber conditions satisfy `D(a + c T) ↔ C(a)` at every point, it carries `Pic^C` onto `Pic^D` on
every `S`-scheme (`FiberCondition.mem_subfunctor_iff_translation`), giving `Pic^C ≅ Pic^D`
(`FiberCondition.subfunctorTranslationIso`; on locally Noetherian test schemes
`FiberCondition.locallyNoetherianSubfunctorTranslationIso`) and the transport of a representation of
`Pic^D` to `Pic^C` (`FiberCondition.representableByOfTranslation`). No hypothesis on `p` or `S` is
used. [Strata/Twist](Strata/Twist.lean): the twist `τ_m : ξ ↦ ξ + o_T(m)` of `Pic_{X/S,(fppf)}`,
with `o_T(m)` the image in `Pic_{X/S,(fppf)}(T)` of the class of `O_{X_T}(m)` (`twistNatIso`,
`twistSection`); for a closed immersion `i` with `ι ≃ Fin (N + 1)` and `f` flat it carries
`Pic^{φ,ψ,r}_m` onto `Pic^{φ₀,ψ,r}_0`, `φ₀ = φ.comp (X - C m)`, on every `S`-scheme
(`mem_fine_iff_twist`), and likewise `Pic^φ_m` onto `Pic^{φ₀}_0` (`mem_coarse_iff_twist`) and the
locus of `C_m` onto that of `C_0` (`mem_coarseLevel_iff_twist`); it induces `Pic^{φ,ψ,r}_m ≅
Pic^{φ₀,ψ,r}_0` (`fineTwistIso`; on locally Noetherian test schemes `fineLocallyNoetherianTwistIso`)
and `Pic^φ_m ≅ Pic^{φ₀}_0` (`coarseTwistIso`), and a representation of `Pic^{φ₀,ψ,r}_0` on locally
Noetherian test schemes by `Q` is one of `Pic^{φ,ψ,r}_m` by `Q` (`fineRepresentableByOfTwist`)
(Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, pp. 29–30, with `φ₀(n) = φ(n - m)` in place of the
printed `φ(m + n)`).

[Strata/DivisorPolynomial](Strata/DivisorPolynomial.lean): for a closed immersion `i` with `ι ≃ Fin
(N + 1)`, a closed subscheme `V ⊆ X_T` flat over `T` (for example a relative effective Cartier
divisor) and a line bundle `L` with `L^{-1} ≅ I_V` (`O(D) ≅ L` for a divisor): `C_φ` for `L` at `t`
is `χ(X_t, (I_V)_t(n)) = φ(n)` for all `n` (`hasFiberDualEulerPolynomial_iff_of_iso`, any `M ≅
L^{-1}`; `hasFiberDualEulerPolynomial_iff_idealModule_comap` with the ideal of the fibre `V_t`);
with `C_ψ` at `t` the fibre at `t` of the image of `V` in `P^N_A ×_{Spec A} T` has Hilbert
polynomial `ψ − φ₀` (`subschemeHilbertPolynomial_comap_pointMap_fromSpecResidueField_eq_sub`); if
`L` satisfies `C_{φ₀}` and `C_ψ` holds at every point, the image of `V` is a point of `Hilb^{ψ −
φ₀}(T)` (`isHilbertFamily_map_immersionBaseChange_of_hasFiberDualEulerPolynomial`) and every
field-point fibre has Hilbert polynomial `θ = ψ − φ₀`
(`subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_hasFiberDualEulerPolynomial`, the fibre
hypothesis of the construction of points of `Div^θ_X`), also from `fineCondition φ₀ ψ m r` at every
point (`Strata.subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_fineCondition_holds`, `f` flat).
Kleiman, arXiv:math/0504020v1, p. 30: "Set `θ(n) := ψ(n) − φ₀(n)`. Plainly `Z` lies in
`Hilb^θ_{X/S}(n)`".

[Strata/DivisorLocus](Strata/DivisorLocus.lean): for a closed immersion `i` with `ι ≃ Fin (N + 1)`
and `f = i ≫ toSpec A ι` flat, a relative effective Cartier divisor whose Abel class satisfies
`fineCondition φ₀ ψ m r` at every point, or whose fppf Abel class lies in `Pic^{φ₀,ψ,r}_m`, is a
point of `Div^{ψ − φ₀}_X` (`Strata.isRelativeDivisorFamily_of_forall_fineCondition_holds_abelClass`,
`Strata.isRelativeDivisorFamily_of_fppfAbelClass_mem_subfunctor_fineCondition`; Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30: "Plainly `Z` lies in `Hilb^θ_{X/S}(n)`"); over a
Noetherian `A`, `Z = Pic^{φ₀,ψ,r}_m ×_P Div^{ψ − φ₀}_X` is represented on locally Noetherian test
schemes by an H-quasi-projective Noetherian scheme, an open subscheme of the scheme of `Div^{ψ −
φ₀}_X` (`Strata.exists_abelPreimage_fineCondition_representableBy`; "Hence `Z` is
quasi-projective").

[Strata/LocalSections](Strata/LocalSections.lean): for a closed immersion `i` with `ι ≃ Fin (N + 1)`
and `f = i ≫ toSpec A ι` flat with geometrically integral fibres, a representation `E` of
`Div^{ψ − φ₀}_X` and `Z = C.abelPreimageOver E` with `C = fineCondition φ₀ ψ 0 (k + 1)`: a line
bundle on `X ×_S V`, `V` locally Noetherian, that satisfies `C` at every point lifts to `Z` over the
Grassmannian bundle `Gr(p_{V*} L, k) ⟶ V`, which is flat, locally of finite presentation and
surjective, with `a^* α_Z = g^*[L]`
(`Strata.exists_lift_abelPreimageOver_of_forall_fineCondition_holds`; the universal divisor of
`LinSys_{L/X_V/V}`, transported by
`LinearSystem.fppfAbelClass_comap_isoPullback_hom_eq_of_isLinearSystemDivisor`); hence the Abel map
`Z ⟶ Pic^{φ₀,ψ,k+1}_0` is fppf-locally surjective on locally Noetherian test schemes
(`Strata.exists_lift_abelPreimageOver_of_mem_subfunctor_fineCondition`), stated, up to the name of
the bound morphism, as hypothesis (h₃) of `Scheme.representableByOfFppfQuotient` for
`G = C.locallyNoetherianSubfunctor` and `z = abelPreimageFppfAbelClass E`. Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30, in the fppf topology: the étale covering `T₁ → T′`
with a map to `P(Q)` is replaced by `T₁ = Gr(p_{V*} L, k)` itself (Kleiman's `P(Q)`); Thm 3.13, pp.
25–26. With `E` given, no Noetherian hypothesis on `A` is used.

[Strata/Relation](Strata/Relation/) proves that `R = Z ×_P Z` is a proper and flat equivalence
relation on `Z = Pic^{φ₀,ψ,k+1}_0 ×_P Div^{ψ − φ₀}_X`, represented by a Grassmannian bundle over `Z`
and closed in `Z ×_S Z` when the representing scheme of `Div^{ψ − φ₀}_X` is separated and locally of
finite type (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8 and of Lemma 4.9, p. 30), for a closed
`X ⊆ P^N_A`, `ι ≃ Fin (N + 1)`, `X ⟶ Spec A` flat with geometrically integral fibres, `A`
Noetherian, and a representation `E` of `Div^{ψ − φ₀}_X` given as data.
[Basic](Strata/Relation/Basic.lean): equal classes in `Pic_{X/S,(fppf)}(T)` differ by a base class
(Thm 2.5(1); `quotientProjection_comp_toFppfPicardSheaf_app_eq_iff`,
`fppfAbelClass_eq_fppfAbelClass_iff`), hence `a^* α_Z = b^* α_Z` iff the classified divisors have
Abel classes differing by a base class
(`FiberCondition.fppfPicardSheaf_map_abelPreimageFppfAbelClass_eq_iff`, any fibre condition); the
functor `FiberCondition.abelRelation` of pairs with the same class.
[LinearSystem](Strata/Relation/LinearSystem.lean): the universal divisor `W_Z` of `Z` and
`𝒪(W_Z) = I_{W_Z}^∨` (class `abelClass W_Z`, condition `C` at every point, fppf class `α_Z`); on the
fine stratum at `m = 0` its direct image has rank `k + 1` with base change, and
`abelRelationBundle e k E = Gr(p_{Z*}𝒪(W_Z), k)` represents `LinSys_{𝒪(W_Z)/X_Z/Z}`
(`abelRelationBundleRepresentableBy`). [Representability](Strata/Relation/Representability.lean):
naturality of `X ×_S U ≅ X_V ×_V U` (`familyMap_comp_isoPullback_hom`), `R = abelRelationOver e k E`
with projections `abelRelationFst` (the bundle map) and `abelRelationSnd` (classifying the
transported universal divisor, of fppf class `pr₁^* α_Z`), `abelRelationι : R ⟶ Z ×_S Z`, and
`abelRelationRepresentableBy : (C.abelRelation E).RepresentableBy R` (with `abelRelation_hom_ext`,
`exists_comp_abelRelationFst_and_comp_abelRelationSnd_iff`).
[Properties](Strata/Relation/Properties.lean): both projections proper and flat (`pr₂ = swap ≫ pr₁`,
`abelRelationSwap`), `R` Noetherian when `Z` is, injectivity and the equivalence relation on locally
Noetherian points of schemes (`abelRelation_left_injective`,
`equivalence_pointsRelation_abelRelation`), and, for `D ⟶ S` separated and locally of finite type,
`IsClosedImmersion (abelRelationι e k E)` and `isEquivalenceRelation_abelRelation`;
`comp_eq_comp_of_fppfPicardSheaf_map_eq_of_abelRelationFst_comp_eq_abelRelationSnd_comp` is
hypothesis (h₁) of `Scheme.representableByOfFppfQuotient` for `z = α_Z`. The focused tests are
`AglibTest.AlgebraicGeometry.Picard.Strata.Relation.*` (with axiom guards).

[Strata/Quotient](Strata/Quotient.lean) applies the fppf form of Kleiman's Lemma 4.9
(`Scheme.representableByOfFppfQuotient`; Kleiman, arXiv:math/0504020v1, end of the proof of Thm 4.8,
p. 30, and Lemma 4.9, pp. 30–31) to `Z = Pic^{φ₀,ψ,k+1}_0 ×_P Div^{ψ − φ₀}_X` and `R = Z ×_P Z`, in
the setting of `Strata/Relation` with `A` Noetherian and the representing scheme `D` of
`Div^{ψ − φ₀}_X` H-quasi-projective. `abelRelation_w`: the projections of `R` agree over `S`;
`abelQuotient e k E`: the flat proper quotient `Q = Z / R` chosen by `nonempty_flatProperQuotient`
(`Q` H-quasi-projective, `q` flat, surjective, proper, `R = Z ×_Q Z`), used through
`(abelQuotient e k E).quotientOver` and `.quotientπ`; `comp_abelQuotientπ_eq_iff`:
`a ≫ q = b ≫ q ↔ a^* α_Z = b^* α_Z` on locally Noetherian points, the pair conditions (h₁), (h₂);
`abelQuotientFppfClass e k E`: the descended class `λ ∈ Pic_{X/S,(fppf)}(Q)`, the unique section
with `q^* λ = α_Z` (`fppfPicardSheaf_map_abelQuotientFppfClass`,
`eq_abelQuotientFppfClass_of_map_eq`), in `Pic^{φ₀,ψ,k+1}_0(Q)`
(`abelQuotientFppfClass_mem_subfunctor`). Given the local lifting property `hloc` of
`α : Z ⟶ Pic^{φ₀,ψ,k+1}_0` (hypothesis (h₃) of `representableByOfFppfQuotient`),
`abelQuotientRepresentableByOfExistsLift e k E hloc` is a representation of
`(fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor` by
`(abelQuotient e k E).quotientOver`, `f ↦ f^* λ`, under which `q` corresponds to `α_Z`;
`exists_fineCondition_representableBy_of_exists_lift` is the existence form.
[Strata/Representability](Strata/Representability.lean) discharges `hloc` by the local sections
([Strata/LocalSections](Strata/LocalSections.lean)): `abelQuotientRepresentableBy e k E` (with
`_homEquiv_coe`, `_homEquiv_quotientπ`) and `exists_fineCondition_representableBy e k E`, **the fine
stratum `Pic^{φ₀,ψ,k+1}_0` is represented on locally Noetherian test schemes by the
H-quasi-projective `Q`**. The focused tests are
`AglibTest.AlgebraicGeometry.Picard.Strata.{Quotient,Representability}` (with axiom guards).

[Scheme/Glue](Scheme/Glue.lean): for a closed immersion `i : X ⟶ P^N_A`, `ι ≃ Fin (N + 1)`,
`p = i ≫ toSpec A ι` flat with geometrically integral fibres, and the premise
`Strata.FineStrataRepresentableByHQuasiProjective i N e` (each `Pic^{φ₀,ψ,k+1}_0` represented on
locally Noetherian test schemes by an H-quasi-projective scheme), the cover
`picardSubfunctorCover h` of `Pic_{X/S,(fppf)}` on locally Noetherian test schemes by the fine
strata `Pic^{φ,ψ,k+1}_m`, indexed by `ULift (ℚ[X] × ℚ[X] × ℤ × ℕ)`, each represented through the
twist (`Strata.fineRepresentableByOfTwist`); the glued `picardScheme h` with
`picardSchemeRepresentableBy h` (`SubfunctorCover.representableByGlued`,
`isZariskiSheaf_fppfPicardSheaf_forget`), the universal section `picardUniversalSection h`
(`picardSchemeRepresentableBy_homEquiv`, `…_homEquiv_id`), the charts as open subfunctors
(`map_picardUniversalSection_mem_iff`) with image the open of `fineCondition φ ψ m (k + 1)`
(`range_picardChart`) and H-quasi-projective structure maps, and `locallyOfFiniteType_picardScheme`.
No Noetherian hypothesis. Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, pp. 28–30; Stacks, Tag
01JJ.

[Scheme/Stratification](Scheme/Stratification.lean): with `ξ` the universal section,
`picardStratumOpens h φ` (open of `C_φ`: open and closed, pairwise disjoint, covering),
`picardLevelOpens h φ m` (open of `C_φ ⊓ C_m`: monotone in `m`, union `picardStratumOpens h φ`),
`picardBaseLevelOpens h φ ψ m` (the disjoint union of the chart images over the ranks), and the
functorial meaning `picardSchemeRepresentableBy_homEquiv_mem_iff` (a morphism lands in the open of
`C` iff its section lies in `Pic^C`). Over a Noetherian `A`, under
`Strata.FiniteFineStrataRanks i N e`, finitely many `(ψ, k)` occur at `(φ, m)`
(`finite_setOf_fineCondition_holds_of_finiteFineStrataRanks`) and
`isHQuasiProjective_picardLevelOpens_of_finiteFineStrataRanks` holds (finite disjoint union,
`IsHQuasiProjective.of_iSup_eq_top_of_pairwise_disjoint`). Kleiman, Thm 4.8 (2), pp. 27–29.

[Scheme/Separated](Scheme/Separated.lean): `isSeparated_picardScheme` (Kleiman, Thm 4.8 (1), proof
p. 28): each `Pic^{φ,ψ}_m` is the disjoint union of separated chart images, and the `Pic^{φ,ψ}_m`
cover, increase with `m` and are disjoint for distinct `(φ, ψ)`
(`isSeparated_of_cover_of_disjoint_of_monotone`). No Noetherian hypothesis, no rank premise.

[Representability](Representability.lean): `exists_representableBy_fppfPicardSheaf_of_fineStrata`
collects target 5 (Kleiman, Thm 4.8, pp. 27–31, fppf form on locally Noetherian test schemes over a
Noetherian `A`) under the two premises.
[Representability/FineStrata](Representability/FineStrata.lean) discharges them
(`Strata.fineStrataRepresentableByHQuasiProjective`, `Strata.finiteFineStrataRanks`, with
`FiberCondition.nonempty_of_holds_of_representableBy`) from
`Strata.exists_fineCondition_representableBy` and the H-quasi-projective Noetherian `Div^{ψ−φ₀}_X`,
and states **`exists_representableBy_fppfPicardSheaf`, target 5 with no premise**: for `A`
Noetherian and a closed `X ⊆ P^N_A` flat over `A` with geometrically integral fibres,
`Pic_{X/S,(fppf)}` on locally Noetherian test schemes is represented by a separated `Spec A`-scheme
locally of finite type, the disjoint union of the open and closed `Pic^φ`, each the increasing union
of the H-quasi-projective opens `Pic^φ_m`. Tests:
`AglibTest.AlgebraicGeometry.Picard.{Scheme.*,Representability,Representability.FineStrata}`.

[Scheme/FieldProperties](Scheme/FieldProperties.lean): the Picard scheme over a field. For any
ring, `ProjectiveSpace.isProper_comp_toSpec_of_isClosedImmersion i e : IsProper (i ≫ toSpec A ι)`
for a closed immersion `i : X ⟶ P^N_A` and `ι ≃ Fin (N + 1)`. For a field `k` and any
representation `e` of `F = Pic_{X/k,(fppf)}` on locally Noetherian test schemes by `P` locally of
finite type over `k`: `unitPoint_eq_unitPoint_picardCommGrpObj` (the point of the section
representing `0`, where `unitStalk e` is taken, is the unit point of the group law
`picardCommGrpObj p P e`); `identityComponent_baseChangeRepresentableBy` (for a field extension `K`
of `k`, the identity component of `P_K`, for its group law as the scheme representing
`Pic_{X_K/K,(fppf)}` through `baseChangeRepresentableBy`, is the preimage of that of `P`; Kleiman,
arXiv:math/0504020v1, Prop. 5.3, p. 37, "forming it commutes with extending `k`", with Ex. 4.4,
p. 27) and `picardIdentityComponentBaseChangeIso : (Pic⁰_{X/k})_K ≅ Pic⁰_{X_K/K}`. At the Picard
scheme `picardScheme h` of a closed `X ⊆ P^N_k`, flat with geometrically integral fibres, with `X`
the `FScheme k` `Over.mk (i ≫ toSpec k ι)`: `picardSchemeTangentKernelLinearEquiv h :
ker(F(k[ε]) → F(k)) ≃ₗ[k] H^1(X, 𝒪_X)` for `a • t = F(µ_a) t` (Kleiman, Thm 5.11, p. 42) and the
Zariski form `picardSchemeCotangentSpaceDualLinearEquiv h : (𝔪/𝔪²)^∨ ≃ₗ[k] H^1(X, 𝒪_X)`; the
statements of [IdentityComponent](IdentityComponent.lean) apply at `picardScheme h` as they stand
(`Pic⁰_{X/k}` open and closed, a group subscheme, of finite type, geometrically irreducible;
Kleiman, Prop. 5.3, p. 37). **`exists_representableBy_fppfPicardSheaf_fieldProperties i e`, target 6
over a field with no premise**: a separated `k`-scheme `P` locally of finite type representing
`Pic_{X/k,(fppf)}` on locally Noetherian test schemes, with `T_0 = H^1(X, 𝒪_X)` in the
tangent-kernel and the Zariski form at the unit point, `Pic⁰_{X/k}` open and closed, a group
subscheme of finite type, geometrically irreducible, and its formation commuting with every field
extension. Instance search does not find `unitStalkAlgebra` at `picardScheme h` (measured; a
candidate cause is that `picardScheme h` is reducible), so the Zariski form supplies it with
`letI := unitStalkAlgebra (picardSchemeRepresentableBy h)`; the group and finiteness instances of
`Pic⁰` are found through those on `identityComponentOver`. The focused test is
`AglibTest.AlgebraicGeometry.Picard.Scheme.FieldProperties` (with axiom guards).

[Scheme/Properties](Scheme/Properties.lean): the basic properties of the Picard scheme over a
Noetherian `A` (target 6 of [PICARD_PLAN.md](../../../docs/PICARD_PLAN.md)). With a section `o` of
`p = i ≫ toSpec A ι`: `picardSchemeNormalizedRepresentableBy h o ho`,
`picardSchemeRigidifiedRepresentableBy h o ho` and, with `IsSplitEpi p`,
`picardSchemeRelativeRepresentableByOfIsSplitEpi h` (each with `_homEquiv`; Kleiman, Thm 2.5(2),
p. 18, Def. 2.8 and Lemma 2.9, p. 19; Stacks, Tag 0B9N); for `g : S' ⟶ Spec A` with `S'` locally
Noetherian, `picardSchemeBaseChangeIso h g e' : P' ≅ P ×_S S'` for every representation `e'` of
`Pic_{X_{S'}/S',(fppf)}` by `P'` on locally Noetherian `S'`-schemes (Kleiman, Ex. 4.4, p. 27, and
Answer 4.4, p. 65; Mathlib's `RepresentableBy.uniqueUpToIso`). The group law `picardCommGrpObj`,
its additivity (`picard_homEquiv_mul`, `picardHomAddEquiv`), the base change
`baseChangeRepresentableBy` and its group law (`picardCommGrpObj_baseChange_toGrpObj`) apply at
`picardScheme h` with no new declaration. **`exists_representableBy_fppfPicardSheaf_basicProperties
i e`, target 6 with no premise**: a separated `Spec A`-scheme `P` locally of finite type with a
representation `R` of `Pic_{X/S,(fppf)}` on locally Noetherian test schemes such that `R` is
additive for `picardCommGrpObj p P R`; with a section, `P` represents the normalized and rigidified
functors, and `P_{X/S}` with `IsSplitEpi p`; for every locally Noetherian `S'` over `S`, the group
law of `P ×_S S'` as the scheme representing `Pic_{X_{S'}/S',(fppf)}` (`baseChangeRepresentableBy`)
is the base-changed one, and every representing scheme is isomorphic to `P ×_S S'`; the strata
`Pic^φ` are open and closed, disjoint and cover `P`, with their functorial meaning; and for every
field point `g : Spec K ⟶ Spec A`, with `X_K = X ×_S Spec K` and `P_K` representing
`Pic_{X_K/K,(fppf)}`: `T_0 = H^1(X_K, 𝒪)` in the tangent-kernel and the Zariski form, the point of
the Zariski form is the unit, and `Pic⁰_{X_K/K}` is open and closed, a group subscheme, of finite
type, geometrically irreducible, and its formation commutes with every field extension `L/K`. For
`A = k` a field the statements for `X` itself are
`exists_representableBy_fppfPicardSheaf_fieldProperties`. The focused test is
`AglibTest.AlgebraicGeometry.Picard.Scheme.Properties` (with axiom guards).

[FiberCondition/Surjective](FiberCondition/Surjective.lean): `Pic^C` descends along every morphism
`g : T' ⟶ T` over `S` that is surjective on points (`FiberCondition.mem_subfunctor_of_map_mem`,
`map_mem_subfunctor_iff_of_surjective`), from `mem_subfunctor_iff` and `holdsAt_map`; no flatness.
This is the descent hypothesis of `Scheme.representableByOfFppfQuotient` for `G =
C.locallyNoetherianSubfunctor`.

[Abel/Basic](Abel/Basic.lean): for an effective Cartier divisor `i : D ⟶ X`,
`IsEffectiveCartier.idealLineBundle` is `I_D` as a line bundle; for a relative effective Cartier
divisor and cartesian squares of the base and the divisor, the canonical comparison `b^* I_D ⟶
I_{D'}` is an isomorphism (`IsRelativeEffectiveCartier.pullbackIdealLineBundleIso`, from
`flatQuotient_idealPullbackMap_isIso`; Kleiman, remark after Def. 3.6, p. 23), with class form
`pullbackClass_classOf_idealLineBundle`. For `D ⊆ X ×_S T` relative effective Cartier over `T` (an
`IdealSheafData` of the literal `pullback p T.hom`), `RelativePicard.abelClass p D hD = −[I_D]`, the
class of `𝒪_{X_T}(D) = I_D^∨` (`abelClass_eq_classOf_dualLineBundle`; Kleiman, Def. 4.6, p. 27).
Naturality: `pullbackClass_abelClass` for any cartesian square `X ×_S T' ⟶ X ×_S T` over `T' ⟶ T`,
and `familyPicardFunctor_map_abelClass` along `(familyScheme p).map g` with `D.comap ((familyScheme
p).map g)` (`isPullback_familyScheme_map`, `isRelativeEffectiveCartier_comap_familyScheme_map`). The
class in `Pic_{X/S,(fppf)}(T)` is `fppfAbelClass`, natural by `fppfPicardSheaf_map_fppfAbelClass`.
No hypothesis on `p`. Sign convention as the curve-level `Scheme.Hom.abelClass`
(EffectiveCartierDivisor/Relative/GraphLineBundle): classes of `𝒪(D)`. The natural transformation
out of `Div^θ` (P7c) is not formed.

[Abel/Divisor](Abel/Divisor.lean): for a preimmersion `i : X ⟶ P^n_A` over `Spec A` (`hi : i ≫
toSpec A ι = πX`) and `θ ∈ ℚ[X]`, the divisor functor `Div^θ_X = relativeDivisorFunctor i hi θ`
pulls divisors back along the maps of `familyScheme πX`
(`ProjectiveSpace.relativeDivisorFunctor_map_coe_eq_comap_familyScheme_map`, `rfl`). A line bundle
`L` represents the Abel class of a relative effective Cartier divisor `D` if and only if `L^∨ ≅ I_D`
(`classOf_eq_abelClass_iff`; one direction
`nonempty_dualLineBundle_iso_idealModule_of_classOf_eq_abelClass`). The Abel map `divisorAbelMap i
hi θ : Div^θ_X ⋙ uliftFunctor ⟶ familyPicardFunctor πX ⋙ forget`, `D ↦ [𝒪(D)] = −[I_D]`, with values
in the absolute Picard functor (the lift to `Type (u + 1)` is forced by the universe of the Picard
groups), and its composite `divisorFppfAbelMap` with the class map to `Pic_{X/S,(fppf)}`, `D ↦
fppfAbelClass πX D`, which is Kleiman's Abel map (arXiv:math/0504020v1, Def. 4.6, p. 27) with its
target `Pic_{X/S}` replaced by the associated fppf sheaf. For a representation `E` of `Div^θ_X` on
locally Noetherian test schemes by `D`, `universalFppfAbelClass E` is the class of the universal
divisor and its pullback along `a : T ⟶ D` is the class of the divisor `E.homEquiv a`
(`fppfPicardSheaf_map_universalFppfAbelClass`). For a fibre condition `C`, `C.abelPreimage i hi θ`
is the subfunctor `Pic^C ×_P Div^θ_X` of the divisors whose fppf Abel class lies in `Pic^C`
(pointwise: `mem_abelPreimage_obj_iff_forall_holds`); on locally Noetherian test schemes it is
represented by the open subscheme `C.abelPreimageOver E = C.opens (universalFppfAbelClass E)` of `D`
(`abelPreimageRepresentableBy`, through `representableByRestrictOpens`; criterion
`homEquiv_mem_abelPreimage_iff`), with universal class `abelPreimageFppfAbelClass` in `Pic^C`, equal
to the class of the universal divisor of the open subscheme (`abelPreimageFppfAbelClass_eq`) and
pulling back to the class of the classified divisor
(`fppfPicardSheaf_map_abelPreimageFppfAbelClass`). Over a Noetherian `A` with `D`
H-quasi-projective, the open subscheme is H-quasi-projective and Noetherian (instances
`isHQuasiProjective_abelPreimageOver_hom`, `isNoetherian_abelPreimageOver`). Kleiman, proof of Thm
4.8, p. 30 ("Form the product `P_0^{φ0} ×_P Div_{X/S}`. It is a scheme `Z`, in fact, an open
subscheme of `Div_{X/S}`"), for any fibre condition.

[ZariskiSheaf](ZariskiSheaf.lean): `(fppfPicardSheaf p).obj ⋙ forget` is a sheaf for
`Scheme.zariskiTopology.over S` (`isSheaf_zariskiTopology_fppfPicardSheaf_forget`), and its
restriction to `Scheme.LocallyNoetherianOver S` satisfies the sheaf hypothesis of
`SubfunctorCover.representableByGlued` (`isZariskiSheaf_fppfPicardSheaf_forget`). No hypothesis on
`p`.

[LinearSystem](LinearSystem/) gives the linear-system functor `LinSys_{L/X/S}` (Kleiman, Def. 3.12,
p. 25, in ideal form: `I_D ≅ q_T^* N ⊗ g_T^* L^∨` for a line bundle `N` on `T`, so Kleiman's `N` is
the dual of this one) and its representability by `Gr(E, r − 1)`, `E = p_* L`, in the locally free
regime (Thm 3.13 and Ex. 3.14, pp. 25–26), for `p` proper, flat and geometrically integral over a
locally Noetherian base, with every base-change map of `L` an isomorphism (statement 15a) and `E` of
constant rank `r ≥ 1`. [Basic](LinearSystem/Basic.lean): `familyMap p t := (familyScheme p).map t`,
typed between the literal fibre products (it equals the `pullback.lift` form `Scheme.Hom.familyMap`
by `RelativePicard.Classes.familyMap_eq_familyScheme_map`), `IsLinearSystemDivisor`,
`linearSystemFunctor` (on all of `Over S`) and `evaluationPairing`.
[Evaluation](LinearSystem/Evaluation.lean): the evaluation map `q_T^* E_T ⟶ g_T^* L` (adjoint of the
base-change map) and its base change. [Divisor](LinearSystem/Divisor.lean): the divisor of a line
subbundle `u : N ⟶ E_T` and of a point of `Gr(E, k)` (`isLinearSystemDivisor_subbundleDivisor`,
`isLinearSystemDivisor_quotientDivisor`), and nonvanishing of sections (`subbundleSection_ne_zero`,
`pullback_fst_map_subbundleSection_ne_zero`). [Bijection](LinearSystem/Bijection.lean): `Gr(E, k)(T)
≃ LinSys(T)` (`quotientDivisorEquiv`); no divisor over a nonempty `T` where `E = 0`
(`isEmpty_of_isLinearSystemDivisor_of_sheafHasRank_zero`).
[Representability](LinearSystem/Representability.lean): `linearSystemRepresentableBy` (all schemes
over `S`), `locallyNoetherianLinearSystemRepresentableBy` (locally Noetherian test schemes),
`exists_representableBy_linearSystemFunctor` (by a scheme proper, smooth and flat over `S`),
`universalLinearSystemDivisor` and its universal property
(`existsUnique_comap_universalLinearSystemDivisor`, Ex. 3.14).
[AbelClass](LinearSystem/AbelClass.lean): the Abel-class form of the linear system: a relative
effective Cartier `D ⊆ X ×_S T` lies in `LinSys_{L/X/S}(T)` iff `abelClass D = g_T^*[L] + p_T^* n`
for a class `n` on `T` (`isLinearSystemDivisor_iff_exists_abelClass_eq`,
`isLinearSystemDivisor_iff_abelClass_sub_mem_baseImage`), so its fppf Abel class is the class of
`g_T^* L` (`fppfAbelClass_eq_of_isLinearSystemDivisor`); two classes have the same image in
`P_{X/S}(T)` iff they differ by a base class (`RelativePicard.quotientProjection_app_eq_iff`); the
transport along `X ×_S U ≅ X_V ×_V U = (isPullback_familyMap p g).isoPullback` for `g : U ⟶ V` of
relative effective Cartier divisors (both directions), Abel classes and base classes
(`RelativePicard.isRelativeEffectiveCartier_comap_isoPullback_hom`, `…_inv`,
`abelClass_comap_isoPullback_hom`, `pullbackClass_isoPullback_hom_mem_baseImage_iff`), and the
linear system over `V` read on `X ×_S U`
(`isLinearSystemDivisor_iff_abelClass_comap_isoPullback_hom_sub_mem_baseImage`,
`fppfAbelClass_comap_isoPullback_hom_eq_of_isLinearSystemDivisor`). No hypothesis on `p`.
Open: representability by `∅` on the `r = 0` piece, gluing over the clopen `h^0` pieces, and the
module form `O(D) ≅ L_T ⊗ p_T^*N` of the divisor class (the class form is `AbelClass`), which F17
does not need.
The focused test is `AglibTest.AlgebraicGeometry.Picard.LinearSystem` (with axiom guards).
