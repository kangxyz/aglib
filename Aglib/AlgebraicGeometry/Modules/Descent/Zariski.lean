/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Descent.Pseudofunctor
public import Aglib.AlgebraicGeometry.Modules.Descent.Substack
public import Aglib.AlgebraicGeometry.Modules.Descent.RestrictPullback
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Homology
public import Aglib.AlgebraicGeometry.Modules.Invertible.Locality
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-!
# Zariski descent for module sheaves

This file concerns the module-sheaf pullback pseudofunctor
`Scheme.Modules.pullbackPseudofunctor` and Mathlib's big Zariski topology
`Scheme.zariskiTopology` (Stacks Project, revision a04446e5, Tag 023E: Zariski descent of
quasi-coherent sheaves is effective and fully faithful; its proof is the gluing of sheaves,
Stacks Section 6.33, Tag 00AK, Lemmas 6.33.2 and 6.33.3, Tags 00AL and 00AM; the tags are
those of Stacks revision a04446e5; their statements were read on the Stacks website on
2026-10-17).

* `isQuasicoherent_of_mem_zariskiTopology`, `isLocallyRankOne_of_mem_zariskiTopology`:
  quasi-coherence and local rank one are local for Zariski covering sieves.
* `isStack_quasicoherentPseudofunctor_of_isStack`, `isStack_lineBundlePseudofunctor_of_isStack`:
  if the module-sheaf pseudofunctor is a Zariski stack, so are its quasi-coherent and
  line-bundle subpseudofunctors.
* `isStack_zariskiTopology_of_opens`: the stack property for `Scheme.zariskiTopology` reduces,
  through Mathlib's `Pseudofunctor.IsStack.of_precoverage`, to the case of open covers
  `U : ι → S.Opens` by their inclusions `(U i).ι`.
* `fullyFaithfulToDescentDataOfOpenImmersion` and the instance `isPrestack_zariskiTopology`:
  morphisms glue along jointly surjective families of open immersions, through Aglib's
  `InternalHom.existsUnique_restrictionHom`; the quasi-coherent and line-bundle
  subpseudofunctors are prestacks as well.
* `isStack_zariskiTopology_of_essSurj`: with the prestack property, the stack property reduces
  to essential surjectivity of `toDescentData (fun i ↦ (U i).ι)` for open covers by opens
  (effective gluing). The gluing is proved in `Descent/ZariskiStack.lean`
  (`projectionSurjective`), which gives the instance
  `isStack_pullbackPseudofunctor_zariskiTopology`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Bicategory Pseudofunctor

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}}

/-- For an open immersion `f`, the restriction of `M` to the range of `f` is the pullback of
`f^* M` along the inverse of the isomorphism `f.isoOpensRange`. -/
def restrictOpensRangeIso {Y : Scheme.{u}} (f : Y ⟶ S) [IsOpenImmersion f] (M : S.Modules) :
    M.restrict f.opensRange.ι ≅ (pullback f.isoOpensRange.inv).obj ((pullback f).obj M) :=
  (restrictFunctorIsoPullback f.opensRange.ι).app M ≪≫
    (pullbackCongr f.isoOpensRange_inv_comp.symm).app M ≪≫
      ((pullbackComp f.isoOpensRange.inv f).app M).symm

/-- Quasi-coherence is local for Zariski covering sieves. -/
theorem isQuasicoherent_of_mem_zariskiTopology {R : Sieve S}
    (hR : R ∈ Scheme.zariskiTopology S) (M : S.Modules)
    (h : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ S), R g → ((pullback g).obj M).IsQuasicoherent) :
    M.IsQuasicoherent := by
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  refine QuasiCoherent.quasicoherent_of_openNeighborhoods M (fun x ↦ ?_)
  refine ⟨(𝒰.f (𝒰.idx x)).opensRange, 𝒰.covers x, ?_⟩
  have := h _ (h𝒰 _ _ (Presieve.ofArrows.mk (𝒰.idx x)))
  exact (SheafOfModules.isQuasicoherent _).prop_of_iso
    (restrictOpensRangeIso (𝒰.f (𝒰.idx x)) M).symm (quasicoherent_pullback _ _)

/-- Local rank one is local for Zariski covering sieves. -/
theorem isLocallyRankOne_of_mem_zariskiTopology {R : Sieve S}
    (hR : R ∈ Scheme.zariskiTopology S) (M : S.Modules)
    (h : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ S), R g →
      Invertible.IsLocallyRankOne Y ((pullback g).obj M)) :
    Invertible.IsLocallyRankOne S M := by
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  refine Invertible.isLocallyRankOne_of_cover_restrict M (fun i ↦ (𝒰.f i).opensRange)
    (Scheme.OpenCover.isOpenCover_opensRange (𝒰 := 𝒰)) (fun i ↦ ?_)
  exact Invertible.isLocallyRankOne_of_iso _ (restrictOpensRangeIso (𝒰.f i) M).symm
    (Invertible.pullback_locallyRankOne _ _ (h _ (h𝒰 _ _ (Presieve.ofArrows.mk i))))

/-- If the module-sheaf pseudofunctor is a Zariski stack, so is its quasi-coherent
subpseudofunctor. -/
theorem isStack_quasicoherentPseudofunctor_of_isStack
    [pullbackPseudofunctor.{u}.IsStack Scheme.zariskiTopology] :
    quasicoherentPseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  ObjectProperty.isStack_fullsubcategory _ fun _ _ hR M hM ↦
    isQuasicoherent_of_mem_zariskiTopology hR M fun _ g hg ↦ hM g hg

/-- If the module-sheaf pseudofunctor is a Zariski stack, so is its line-bundle
subpseudofunctor. -/
theorem isStack_lineBundlePseudofunctor_of_isStack
    [pullbackPseudofunctor.{u}.IsStack Scheme.zariskiTopology] :
    lineBundlePseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  ObjectProperty.isStack_fullsubcategory _ fun _ _ hR M hM ↦
    isLocallyRankOne_of_mem_zariskiTopology hR M fun _ g hg ↦ hM g hg

/-- The sieve generated by a family of open immersions is the sieve generated by the
inclusions of their ranges. -/
lemma sieve_ofArrows_eq_opensRange {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] :
    Sieve.ofArrows X f = Sieve.ofArrows (fun i ↦ (f i).opensRange.toScheme)
      (fun i ↦ (f i).opensRange.ι) := by
  apply le_antisymm
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact ⟨_, (f i).isoOpensRange.hom, _, ⟨i⟩, (f i).isoOpensRange_hom_ι⟩
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact ⟨_, (f i).isoOpensRange.inv, _, ⟨i⟩, (f i).isoOpensRange_inv_comp⟩

/-- The Zariski stack property of the module-sheaf pseudofunctor reduces to open covers of a
scheme by opens: it suffices that `toDescentData` is an equivalence for the inclusions
`(U i).ι` of every family of opens with `iSup U = ⊤`. -/
theorem isStack_zariskiTopology_of_opens
    (h : ∀ (S : Scheme.{u}) (ι : Type (u + 1)) (U : ι → S.Opens), iSup U = ⊤ →
      (pullbackPseudofunctor.{u}.toDescentData (fun i ↦ (U i).ι)).IsEquivalence) :
    pullbackPseudofunctor.{u}.IsStack Scheme.zariskiTopology := by
  refine IsStack.of_precoverage (J := Scheme.zariskiPrecoverage) fun S R hR ↦ ?_
  obtain ⟨ι, X, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Scheme.ofArrows_mem_precoverage_iff] at hR
  obtain ⟨hsurj, hopen⟩ := hR
  have : ∀ i, IsOpenImmersion (f i) := hopen
  rw [isStackFor_ofArrows_iff, DescentData.isEquivalence_toDescentData_iff_of_sieve_eq _ f _
    (sieve_ofArrows_eq_opensRange f)]
  refine h S ι (fun i ↦ (f i).opensRange) ?_
  refine top_unique fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := hsurj x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

section Prestack

-- The descent-datum morphisms live in `pullbackPseudofunctor.obj _` (a `Cat.of`); matching them
-- with `pullbackComp` terms in `X.Modules` needs relaxed instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- The descent datum of an object, in terms of Mathlib's `pullbackComp` and `pullbackCongr`. -/
lemma pullbackPseudofunctor_toDescentData_obj_hom {ι : Type*} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (M : S.Modules) {Y : Scheme.{u}} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((pullbackPseudofunctor.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ =
      (pullbackComp f₁ (f i₁)).hom.app M ≫ (pullbackCongr hf₁).hom.app M ≫
        (pullbackCongr hf₂.symm).hom.app M ≫ (pullbackComp f₂ (f i₂)).inv.app M := by
  have h₁ := pullbackPseudofunctor_mapComp'_inv_app (f i₁) f₁ q hf₁ M
  have h₂ := pullbackPseudofunctor_mapComp'_hom_app (f i₂) f₂ q hf₂ M
  refine (congrArg₂ (fun a b ↦ a ≫ b) h₁ h₂).trans ?_
  simp only [Category.assoc]

/-- For open immersions `b` and `a`, the double restriction of `M` is identified with the double
pullback through `restrictFunctorIsoPullback`. -/
def restrictRestrictIso {X Y Z : Scheme.{u}} (b : Z ⟶ Y) (a : Y ⟶ X) [IsOpenImmersion a]
    [IsOpenImmersion b] (M : X.Modules) :
    (M.restrict a).restrict b ≅ (pullback b).obj ((pullback a).obj M) :=
  (restrictFunctor b).mapIso ((restrictFunctorIsoPullback a).app M) ≪≫
    (restrictFunctorIsoPullback b).app _

lemma restrictRestrictIso_hom_naturality {X Y Z : Scheme.{u}} (b : Z ⟶ Y) (a : Y ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] {M N : X.Modules}
    (φ : (pullback a).obj M ⟶ (pullback a).obj N) :
    (restrictFunctor b).map ((restrictFunctorIsoPullback a).hom.app M ≫ φ ≫
        (restrictFunctorIsoPullback a).inv.app N) ≫ (restrictRestrictIso b a N).hom =
      (restrictRestrictIso b a M).hom ≫ (pullback b).map φ := by
  dsimp only [restrictRestrictIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  have : (restrictFunctorIsoPullback a).hom.app M ≫ φ ≫
      (restrictFunctorIsoPullback a).inv.app N ≫ (restrictFunctorIsoPullback a).hom.app N =
      (restrictFunctorIsoPullback a).hom.app M ≫ φ := by
    rw [Iso.inv_hom_id_app, Category.comp_id]
  rw [← Category.assoc, ← Functor.map_comp, Category.assoc, Category.assoc, this,
    Functor.map_comp, Category.assoc, (restrictFunctorIsoPullback b).hom.naturality φ]
  rfl

/-- Through `restrictRestrictIso`, Aglib's overlap identification `overlapRestrictIso` is the
canonical pullback identification `pullbackComp`/`pullbackCongr`/`pullbackComp`. -/
lemma overlapRestrictIso_hom_app_restrictRestrictIso_hom {Y₁ Y₂ : Scheme.{u}} (a₁ : Y₁ ⟶ S)
    (a₂ : Y₂ ⟶ S) [IsOpenImmersion a₁] [IsOpenImmersion a₂] (M : S.Modules) :
    (overlapRestrictIso a₁ a₂).hom.app M ≫
        (restrictRestrictIso (Limits.pullback.snd a₁ a₂) a₂ M).hom =
      (restrictRestrictIso (Limits.pullback.fst a₁ a₂) a₁ M).hom ≫
        (pullbackComp (Limits.pullback.fst a₁ a₂) a₁).hom.app M ≫
          (pullbackCongr Limits.pullback.condition).hom.app M ≫
            (pullbackComp (Limits.pullback.snd a₁ a₂) a₂).inv.app M := by
  have c₁ := restrictFunctorIsoPullback_comp_hom_app (Limits.pullback.fst a₁ a₂) a₁ M
  have c₂ := restrictFunctorIsoPullback_comp_hom_app (Limits.pullback.snd a₁ a₂) a₂ M
  have c₃ := restrictFunctorIsoPullback_congr_hom_app
    (Limits.pullback.condition (f := a₁) (g := a₂)) M
  have e₁ : (restrictRestrictIso (Limits.pullback.fst a₁ a₂) a₁ M).hom =
      (restrictFunctorComp (Limits.pullback.fst a₁ a₂) a₁).inv.app M ≫
        (restrictFunctorIsoPullback (Limits.pullback.fst a₁ a₂ ≫ a₁)).hom.app M ≫
          (pullbackComp (Limits.pullback.fst a₁ a₂) a₁).inv.app M := by
    rw [c₁, Iso.inv_hom_id_app_assoc]
    rfl
  have e₂ : (restrictRestrictIso (Limits.pullback.snd a₁ a₂) a₂ M).hom =
      (restrictFunctorComp (Limits.pullback.snd a₁ a₂) a₂).inv.app M ≫
        (restrictFunctorIsoPullback (Limits.pullback.snd a₁ a₂ ≫ a₂)).hom.app M ≫
          (pullbackComp (Limits.pullback.snd a₁ a₂) a₂).inv.app M := by
    rw [c₂, Iso.inv_hom_id_app_assoc]
    rfl
  rw [e₁, e₂]
  simp only [overlapRestrictIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% c₃]

-- `pullHom` is formed in `pullbackPseudofunctor.obj _`; rewriting it with `pullbackComp` terms in
-- `X.Modules` needs relaxed instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- Restriction form of `pullHom`: for open immersions `a`, `b`, `c`, transporting
`pullHom φ c (c ≫ a) (c ≫ b)` through `restrictFunctorIsoPullback` gives the restriction along
`c` of the transported `φ`, up to `restrictFunctorComp`. This is the coherence needed to compare
descent-datum transitions on nested opens. -/
lemma pullbackPseudofunctor_pullHom_restrict {X₁ X₂ Y Y' : Scheme.{u}} (a : Y ⟶ X₁)
    (b : Y ⟶ X₂) (c : Y' ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    (φ : (pullback a).obj M₁ ⟶ (pullback b).obj M₂) :
    (restrictFunctorIsoPullback (c ≫ a)).hom.app M₁ ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pullbackPseudofunctor) φ c
          (c ≫ a) (c ≫ b) rfl rfl ≫ (restrictFunctorIsoPullback (c ≫ b)).inv.app M₂ =
      (restrictFunctorComp c a).hom.app M₁ ≫
        (restrictFunctor c).map ((restrictFunctorIsoPullback a).hom.app M₁ ≫ φ ≫
          (restrictFunctorIsoPullback b).inv.app M₂) ≫
        (restrictFunctorComp c b).inv.app M₂ := by
  have h₁ := pullbackPseudofunctor_mapComp'_hom_app a c (c ≫ a) rfl M₁
  have h₂ := pullbackPseudofunctor_mapComp'_inv_app b c (c ≫ b) rfl M₂
  have c₁ := restrictFunctorIsoPullback_comp_hom_app c a M₁
  have c₂ := restrictFunctorIsoPullback_comp_hom_app c b M₂
  have hc : (pullbackCongr (rfl : c ≫ a = c ≫ a)).hom.app M₁ = 𝟙 _ := by simp [pullbackCongr]
  have hc' : (pullbackCongr (rfl : c ≫ b = c ≫ b)).hom.app M₂ = 𝟙 _ := by simp [pullbackCongr]
  have e : Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pullbackPseudofunctor) φ c
      (c ≫ a) (c ≫ b) rfl rfl = (pullbackComp c a).inv.app M₁ ≫ (pullback c).map φ ≫
        (pullbackComp c b).hom.app M₂ := by
    refine (congrArg₂ (fun x y ↦ x ≫ (pullback c).map φ ≫ y) h₁ h₂).trans ?_
    simp only [hc, hc', Category.id_comp, Category.comp_id]
  rw [e, ← cancel_mono ((restrictFunctorIsoPullback (c ≫ b)).hom.app M₂ ≫
    (pullbackComp c b).inv.app M₂)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app]
  rw [c₂, reassoc_of% c₁, ← reassoc_of% ((restrictFunctorIsoPullback c).hom.naturality φ)]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj]

variable {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)]

/-- The local arrows in restriction form attached to a morphism of descent data. -/
def descentDataHomRestrict {M N : S.Modules}
    (Φ : (pullbackPseudofunctor.toDescentData f).obj M ⟶
      (pullbackPseudofunctor.toDescentData f).obj N) (i : ι) :
    M.restrict (f i) ⟶ N.restrict (f i) :=
  (restrictFunctorIsoPullback (f i)).hom.app M ≫ Φ.hom i ≫
    (restrictFunctorIsoPullback (f i)).inv.app N

-- The descent-datum compatibility is stated in `pullbackPseudofunctor.obj _`; rewriting it with
-- module-sheaf identities needs relaxed instance transparency.
set_option backward.isDefEq.respectTransparency false in
lemma restrictionHomCompatible_descentDataHomRestrict {M N : S.Modules}
    (Φ : (pullbackPseudofunctor.toDescentData f).obj M ⟶
      (pullbackPseudofunctor.toDescentData f).obj N) :
    InternalHom.RestrictionHomCompatible f M N (descentDataHomRestrict f Φ) := by
  intro i k
  let p₁ := Limits.pullback.fst (f i) (f k)
  let p₂ := Limits.pullback.snd (f i) (f k)
  have hΦ := Φ.comm (p₁ ≫ f i) p₁ p₂ rfl Limits.pullback.condition.symm
  rw [pullbackPseudofunctor_toDescentData_obj_hom,
    pullbackPseudofunctor_toDescentData_obj_hom] at hΦ
  have hrfl (P : S.Modules) : (pullbackCongr (rfl : p₁ ≫ f i = p₁ ≫ f i)).hom.app P = 𝟙 _ := by
    simp [pullbackCongr]
  rw [hrfl, hrfl, Category.id_comp, Category.id_comp] at hΦ
  simp only [Category.assoc] at hΦ
  have n₁ := restrictRestrictIso_hom_naturality p₁ (f i) (M := M) (N := N) (Φ.hom i)
  have n₂ := restrictRestrictIso_hom_naturality p₂ (f k) (M := M) (N := N) (Φ.hom k)
  have o₁ := overlapRestrictIso_hom_app_restrictRestrictIso_hom (f i) (f k) M
  have o₂ := overlapRestrictIso_hom_app_restrictRestrictIso_hom (f i) (f k) N
  rw [← cancel_mono (restrictRestrictIso p₂ (f k) N).hom, Category.assoc, o₂]
  change (restrictFunctor p₁).map ((restrictFunctorIsoPullback (f i)).hom.app M ≫ Φ.hom i ≫
      (restrictFunctorIsoPullback (f i)).inv.app N) ≫ _ = (_ ≫ (restrictFunctor p₂).map
        ((restrictFunctorIsoPullback (f k)).hom.app M ≫ Φ.hom k ≫
          (restrictFunctorIsoPullback (f k)).inv.app N)) ≫ _
  rw [reassoc_of% n₁, Category.assoc, n₂, reassoc_of% o₁]
  congr 1

variable (hf : ∀ x : S, ∃ (i : ι) (y : X i), f i y = x)

/-- The morphism of module sheaves glued from a morphism of descent data along a jointly
surjective family of open immersions. -/
def descentDataHomGlue {M N : S.Modules}
    (Φ : (pullbackPseudofunctor.toDescentData f).obj M ⟶
      (pullbackPseudofunctor.toDescentData f).obj N) : M ⟶ N :=
  InternalHom.glueRestrictionHom X f hf M N (descentDataHomRestrict f Φ)
    (restrictionHomCompatible_descentDataHomRestrict f Φ)

-- As for `restrictionHomCompatible_descentDataHomRestrict`.
set_option backward.isDefEq.respectTransparency false in
lemma toDescentData_map_descentDataHomGlue {M N : S.Modules}
    (Φ : (pullbackPseudofunctor.toDescentData f).obj M ⟶
      (pullbackPseudofunctor.toDescentData f).obj N) :
    (pullbackPseudofunctor.toDescentData f).map (descentDataHomGlue f hf Φ) = Φ := by
  ext i
  have h := InternalHom.glueRestrictionHom_restrict X f hf M N _
    (restrictionHomCompatible_descentDataHomRestrict f Φ) i
  have nat := (restrictFunctorIsoPullback (f i)).hom.naturality (descentDataHomGlue f hf Φ)
  change (pullback (f i)).map (descentDataHomGlue f hf Φ) = Φ.hom i
  rw [← cancel_epi ((restrictFunctorIsoPullback (f i)).hom.app M)]
  refine nat.symm.trans ?_
  rw [descentDataHomGlue, h, descentDataHomRestrict]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rfl

lemma descentDataHomGlue_toDescentData_map {M N : S.Modules} (F : M ⟶ N) :
    descentDataHomGlue f hf ((pullbackPseudofunctor.toDescentData f).map F) = F := by
  symm
  apply InternalHom.glueRestrictionHom_unique
  intro i
  rw [descentDataHomRestrict]
  change _ = _ ≫ (pullback (f i)).map F ≫ _
  rw [← (restrictFunctorIsoPullback (f i)).hom.naturality_assoc, Iso.hom_inv_id_app,
    Category.comp_id]

/-- For a jointly surjective family of open immersions, `toDescentData` is fully faithful:
compatible morphisms of descent data glue uniquely (Aglib's
`InternalHom.existsUnique_restrictionHom`). -/
def fullyFaithfulToDescentDataOfOpenImmersion :
    (pullbackPseudofunctor.toDescentData f).FullyFaithful where
  preimage Φ := descentDataHomGlue f hf Φ
  map_preimage Φ := toDescentData_map_descentDataHomGlue f hf Φ
  preimage_map F := descentDataHomGlue_toDescentData_map f hf F

end Prestack

/-- Module sheaves form a prestack for the Zariski topology: morphisms glue along Zariski
coverings. This is the full-faithfulness half of Stacks Project (revision a04446e5),
Tag 023E, which states it for
quasi-coherent sheaves; no quasi-coherence is used here. -/
instance isPrestack_zariskiTopology :
    pullbackPseudofunctor.{u}.IsPrestack Scheme.zariskiTopology :=
  IsPrestack.of_precoverage (J := Scheme.zariskiPrecoverage) fun S R hR ↦ by
    obtain ⟨ι, X, f, rfl⟩ := R.exists_eq_ofArrows
    rw [Scheme.ofArrows_mem_precoverage_iff] at hR
    obtain ⟨hsurj, hopen⟩ := hR
    have : ∀ i, IsOpenImmersion (f i) := hopen
    rw [isPrestackFor_ofArrows_iff]
    exact ⟨fullyFaithfulToDescentDataOfOpenImmersion f fun x ↦ by
      obtain ⟨i, hi⟩ := hsurj x
      exact ⟨i, hi⟩⟩

/-- Quasi-coherent sheaves form a prestack for the Zariski topology. -/
instance isPrestack_quasicoherentPseudofunctor_zariskiTopology :
    quasicoherentPseudofunctor.{u}.IsPrestack Scheme.zariskiTopology :=
  ObjectProperty.isPrestack_fullsubcategory _

/-- Line bundles form a prestack for the Zariski topology. -/
instance isPrestack_lineBundlePseudofunctor_zariskiTopology :
    lineBundlePseudofunctor.{u}.IsPrestack Scheme.zariskiTopology :=
  ObjectProperty.isPrestack_fullsubcategory _

/-- The Zariski stack property of module sheaves reduces to effectivity of descent data for
open covers by opens. -/
theorem isStack_zariskiTopology_of_essSurj
    (h : ∀ (S : Scheme.{u}) (ι : Type (u + 1)) (U : ι → S.Opens), iSup U = ⊤ →
      (pullbackPseudofunctor.{u}.toDescentData (fun i ↦ (U i).ι)).EssSurj) :
    pullbackPseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  isStack_zariskiTopology_of_opens fun S ι U hU ↦ by
    have hcov : ∀ x : S, ∃ (i : ι) (y : (U i).toScheme), (U i).ι y = x := fun x ↦ by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)
      exact ⟨i, ⟨x, hi⟩, rfl⟩
    have hff := fullyFaithfulToDescentDataOfOpenImmersion (fun i ↦ (U i).ι) hcov
    have := hff.full
    have := hff.faithful
    have := h S ι U hU
    exact { }

end AlgebraicGeometry.Scheme.Modules
