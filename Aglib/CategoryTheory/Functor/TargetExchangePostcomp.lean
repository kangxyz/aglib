/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Postcomposition of a canonical target-transport exchange square -/

@[expose] public noncomputable section
open CategoryTheory.Functor
namespace CategoryTheory
variable {A B A' T₀ T₁ : Type*}
  [Category* A] [Category* B] [Category* A'] [Category* T₀] [Category* T₁]
  {F : A ⥤ B} {G₀ : B ⥤ T₀} {G₁ : B ⥤ T₁} {U : A ⥤ A'}
  {V₀ W₀ : A' ⥤ T₀} {V₁ W₁ : A' ⥤ T₁} {E : T₀ ⥤ T₁}

/-- Appending an original target comparison preserves its canonical target-transport square. -/
theorem targetExchange_postcomp
    (β₀ : F ⋙ G₀ ≅ U ⋙ V₀) (β₁ : F ⋙ G₁ ≅ U ⋙ V₁)
    (δ₀ : V₀ ≅ W₀) (δ₁ : V₁ ≅ W₁)
    (s : G₀ ⋙ E ≅ G₁) (t : V₀ ⋙ E ≅ V₁) (w : W₀ ⋙ E ≅ W₁)
    (hβ : isoWhiskerRight β₀ E ≪≫ associator _ _ _ ≪≫ isoWhiskerLeft U t =
      associator _ _ _ ≪≫ isoWhiskerLeft F s ≪≫ β₁)
    (hδ : isoWhiskerRight δ₀ E ≪≫ w = t ≪≫ δ₁) :
    isoWhiskerRight (β₀ ≪≫ isoWhiskerLeft U δ₀) E ≪≫
        associator _ _ _ ≪≫ isoWhiskerLeft U w =
      associator _ _ _ ≪≫ isoWhiskerLeft F s ≪≫ (β₁ ≪≫ isoWhiskerLeft U δ₁) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hb := congrArg (fun z => z.hom.app K) hβ
  have hd := congrArg (fun z => z.hom.app (U.obj K)) hδ
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, associator_hom_app,
    Category.id_comp] at hb hd ⊢
  rw [Functor.map_comp, Category.assoc, hd, ← Category.assoc, hb]
  simp only [Category.assoc]

end CategoryTheory
