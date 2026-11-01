/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CartesianSourceExchange
public import Aglib.CategoryTheory.NatTrans.SourceIsoComposition
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uB uC uD vA vB vC vD

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vA} A]
  [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
  {F : A ⥤ D} {G : B ⥤ D} {H : C ⥤ D} {I : D ⥤ D}
  {V : A ⥤ B} {E : B ⥤ C} {W Z : A ⥤ C}

/-- Composition of the actual source comparisons cancels the actual source
compositor. Neither the source law nor its equality transport is replaced. -/
theorem cartesianSourceExchange_identity
    (n : F ⋙ I ≅ F) (β : F ⋙ I ≅ V ⋙ G)
    (s₀ : F ≅ V ⋙ G) (s₁ : G ≅ E ⋙ H) (s : F ≅ Z ⋙ H)
    (c : W ≅ V ⋙ E) (d : Z ≅ V ⋙ E) (q : W ≅ Z)
    (hβ : β = n ≪≫ s₀)
    (hs : SourceIsoCompositionEquation s₀ s₁ s (𝟙 H) d)
    (hc : q ≪≫ d = c) :
    cartesianSourceExchange β s₁ c = n ≪≫ s ≪≫ Functor.isoWhiskerRight q.symm H := by
  subst β
  subst c
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hsK := hs K
  dsimp only [Functor.comp_obj, NatTrans.id_app] at hsK
  simp only [Category.id_comp] at hsK
  simp only [cartesianSourceExchange_hom_app, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom]
  calc
    _ = n.hom.app K ≫ (s₀.hom.app K ≫ s₁.hom.app (V.obj K)) ≫
        H.map (d.inv.app K ≫ q.inv.app K) := by simp only [Category.assoc]
    _ = n.hom.app K ≫ (s.hom.app K ≫ H.map (d.hom.app K)) ≫
        H.map (d.inv.app K ≫ q.inv.app K) := by rw [← hsK]
    _ = _ := by
      simp only [Category.assoc, ← H.map_comp, Iso.hom_inv_id_app_assoc]

/-- Whole identity normalization with the original exchange and forward transport. -/
def CartesianSourceIdentityEquation
    {A : Type uA} {C : Type uC} {D : Type uD} [Category.{vA} A] [Category.{vC} C] [Category.{vD} D]
    {F : A ⥤ D} {H : C ⥤ D} {I : D ⥤ D} {W Z : A ⥤ C}
    (β : F ⋙ I ≅ W ⋙ H) (n : F ⋙ I ≅ F)
    (s : F ≅ Z ⋙ H) (q : Z ≅ W) : Prop :=
  β = n ≪≫ s ≪≫ Functor.isoWhiskerRight q H

theorem cartesianIdentity_forward_transport
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vA} A] [Category.{vB} B]
    [Category.{vC} C] [Category.{vD} D]
    {F : A ⥤ D} {G : B ⥤ D} {H : C ⥤ D} {I : D ⥤ D}
    {V : A ⥤ B} {E : B ⥤ C} {W Z : A ⥤ C}
    (n : F ⋙ I ≅ F) (β : F ⋙ I ≅ V ⋙ G)
    (s₀ : F ≅ V ⋙ G) (s₁ : G ≅ E ⋙ H) (s : F ≅ Z ⋙ H)
    (c : W ≅ V ⋙ E) (d : Z ≅ V ⋙ E) (q : Z ≅ W)
    (βout : F ⋙ I ≅ W ⋙ H) (hout : βout = cartesianSourceExchange β s₁ c)
    (hβ : β = n ≪≫ s₀)
    (hs : SourceIsoCompositionEquation s₀ s₁ s (𝟙 H) d)
    (hc : q.symm ≪≫ d = c) :
    CartesianSourceIdentityEquation βout n s q := by
  subst βout
  exact cartesianSourceExchange_identity n β s₀ s₁ s c d q.symm hβ hs hc

theorem cartesianIdentity_eqToIso_symm_comp
    {A : Type uA} {C : Type uC} [Category.{vC} C] (F : A → C) {a b : A} (h : a = b)
    {Z : C} (d : F a ≅ Z) :
    (eqToIso (congrArg F h)).symm ≪≫ d = eqToIso (congrArg F h.symm) ≪≫ d := by
  cases h
  rfl

end CategoryTheory
