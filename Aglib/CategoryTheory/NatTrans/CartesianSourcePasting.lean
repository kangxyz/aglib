/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CartesianSourceExchange
public import Aglib.CategoryTheory.NatTrans.NormalizedIteration
public import Aglib.CategoryTheory.NatTrans.SourceIsoBaseChange
public import Aglib.CategoryTheory.NatTrans.SourceIsoComposition
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uL₁ uA₁ uL₂ uA₂ uLs uB uB₁ uB₂ vA vL₁ vA₁ vL₂ vA₂ vLs vB vB₁ vB₂

variable {A : Type uA} {L₁ : Type uL₁} {A₁ : Type uA₁} {L₂ : Type uL₂} {A₂ : Type uA₂}
  {Ls : Type uLs} {B : Type uB} {B₁ : Type uB₁} {B₂ : Type uB₂}
  [Category.{vA} A] [Category.{vL₁} L₁] [Category.{vA₁} A₁] [Category.{vL₂} L₂] [Category.{vA₂} A₂]
  [Category.{vLs} Ls] [Category.{vB} B] [Category.{vB₁} B₁] [Category.{vB₂} B₂]
  {F : A ⥤ B} {FL : L₁ ⥤ B₁} {F₁ : A₁ ⥤ B₁} {FLL : L₂ ⥤ B₂}
  {F₂ : A₂ ⥤ B₂} {Fs : Ls ⥤ B₂}
  {G₁ : B ⥤ B₁} {G₂ : B₁ ⥤ B₂} {G : B ⥤ B₂}
  {V₁ : A ⥤ L₁} {E₁ : L₁ ⥤ A₁} {W₁ : A ⥤ A₁}
  {V₂ : L₁ ⥤ L₂} {W₂ : A₁ ⥤ A₂} {Q : L₂ ⥤ A₂}
  {Vs : A ⥤ Ls} {Es : Ls ⥤ L₂} {Et : Ls ⥤ A₂}
  {H : A ⥤ L₂} {Ht : A ⥤ A₂}

/-- The full original source polygon; its factors are actual source-square,
literal iteration, and source-composition comparators. -/
def cartesianPastingSourceIso
    (q : W₁ ≅ V₁ ⋙ E₁) (ξ : E₁ ⋙ W₂ ≅ V₂ ⋙ Q)
    (r : V₁ ⋙ V₂ ≅ Vs ⋙ Es) (d : Et ≅ Es ⋙ Q) :
    W₁ ⋙ W₂ ≅ Vs ⋙ Et :=
  Functor.isoWhiskerRight q W₂ ≪≫ Functor.associator V₁ E₁ W₂ ≪≫
    Functor.isoWhiskerLeft V₁ ξ ≪≫ (Functor.associator V₁ V₂ Q).symm ≪≫
    Functor.isoWhiskerRight r Q ≪≫ Functor.associator Vs Es Q ≪≫
    Functor.isoWhiskerLeft Vs d.symm

theorem pastingSource_hom_app
    (q : W₁ ≅ V₁ ⋙ E₁) (ξ : E₁ ⋙ W₂ ≅ V₂ ⋙ Q)
    (r : V₁ ⋙ V₂ ≅ Vs ⋙ Es) (d : Et ≅ Es ⋙ Q) (K : A) :
    (cartesianPastingSourceIso q ξ r d).hom.app K =
      W₂.map (q.hom.app K) ≫ ξ.hom.app (V₁.obj K) ≫
        Q.map (r.hom.app K) ≫ d.inv.app (Vs.obj K) := by
  simp only [cartesianPastingSourceIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp]

/-- Original literal iteration, actual source/base-change interchange, and actual
source composition imply iteration for the transported Cartesian presentations.
The last hypothesis is solely the original inverse-image source polygon. -/
theorem cartesianSourceExchange_pasting
    (β₁ : F ⋙ G₁ ≅ V₁ ⋙ FL) (β₂ : FL ⋙ G₂ ⟶ V₂ ⋙ FLL)
    (β₂' : F₁ ⋙ G₂ ⟶ W₂ ⋙ F₂) (βs : F ⋙ G ⟶ Vs ⋙ Fs)
    (s₁ : FL ≅ E₁ ⋙ F₁) (q : W₁ ≅ V₁ ⋙ E₁)
    (t : FLL ≅ Q ⋙ F₂) (ξ : E₁ ⋙ W₂ ≅ V₂ ⋙ Q)
    (si : Fs ≅ Es ⋙ FLL) (st : Fs ≅ Et ⋙ F₂)
    (γ : G ≅ G₁ ⋙ G₂) (δ : H ≅ V₁ ⋙ V₂) (η : H ≅ Vs ⋙ Es)
    (d : Et ≅ Es ⋙ Q) (δt : Ht ≅ W₁ ⋙ W₂) (ηt : Ht ≅ Vs ⋙ Et)
    (hp : OriginalNormalizedIterationEquation β₁.hom β₂ βs γ δ η si (𝟙 FLL))
    (hb : SourceIsoBaseChangeEquation s₁ β₂' β₂ t ξ)
    (hs : SourceIsoCompositionEquation si t st (𝟙 F₂) d)
    (hρ : cartesianPastingSourceIso q ξ (δ.symm ≪≫ η) d = δt.symm ≪≫ ηt) :
    OriginalNormalizedIterationEquation (cartesianSourceExchange β₁ s₁ q).hom β₂' βs
      γ δt ηt st (𝟙 F₂) := by
  intro K
  have hpK := hp K
  have hsK := hs (Vs.obj K)
  dsimp only [Functor.comp_obj, NatTrans.id_app] at hpK hsK ⊢
  simp only [Category.comp_id] at hpK ⊢
  simp only [Category.id_comp] at hsK
  have hn := β₂'.naturality (q.inv.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  have hq : G₂.map (F₁.map (q.inv.app K)) ≫ β₂'.app (W₁.obj K) ≫
      F₂.map (W₂.map (q.hom.app K)) = β₂'.app (E₁.obj (V₁.obj K)) := by
    rw [← Category.assoc, hn]
    simp only [Category.assoc, ← F₂.map_comp, ← W₂.map_comp, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj]
    simp only [W₂.map_id, F₂.map_id, Category.comp_id]
  have ht := t.hom.naturality ((δ.symm ≪≫ η).hom.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at ht
  rw [← hρ, pastingSource_hom_app, cartesianSourceExchange_hom_app]
  simp only [G₂.map_comp, F₂.map_comp, Category.assoc]
  rw [reassoc_of% hq, reassoc_of% (hb (V₁.obj K)), ← reassoc_of% ht,
    reassoc_of% hpK, ← reassoc_of% hsK]
  simp only [← F₂.map_comp, Iso.hom_inv_id_app, F₂.map_id, Category.comp_id]

end CategoryTheory
