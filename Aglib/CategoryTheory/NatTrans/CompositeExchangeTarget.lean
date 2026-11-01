/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CompositeExchange

/-! # Target-model coherence for an original composite exchange -/

@[expose] public noncomputable section
namespace CategoryTheory
open CategoryTheory.Functor
variable {A B C A' B' T₀ T₁ : Type*}
  [Category* A] [Category* B] [Category* C] [Category* A'] [Category* B']
  [Category* T₀] [Category* T₁]
  {J : A ⥤ B} {R : B ⥤ C} {G₀ : C ⥤ T₀} {G₁ : C ⥤ T₁}
  {H : B ⥤ B'} {R₀ : B' ⥤ T₀} {R₁ : B' ⥤ T₁} {G' : A ⥤ A'} {J' : A' ⥤ B'}
  {E : T₀ ⥤ T₁}

/-- Target transport of a pasted exchange follows from the original right-exchange square;
the original left exchange is unchanged. -/
theorem compositeExchange_target
    (β₀ : R ⋙ G₀ ⟶ H ⋙ R₀) (β₁ : R ⋙ G₁ ⟶ H ⋙ R₁)
    (e : J ⋙ H ≅ G' ⋙ J') (s : G₀ ⋙ E ≅ G₁) (t : R₀ ⋙ E ≅ R₁)
    (h : whiskerRight β₀ E ≫ (associator _ _ _).hom ≫ whiskerLeft H t.hom =
      (associator _ _ _).hom ≫ whiskerLeft R s.hom ≫ β₁) :
    whiskerRight (compositeExchange β₀ e) E ≫ (associator _ _ _).hom ≫
        whiskerLeft G' ((associator _ _ _).hom ≫ whiskerLeft J' t.hom) =
      (associator _ _ _).hom ≫ whiskerLeft (J ⋙ R) s.hom ≫ compositeExchange β₁ e := by
  apply NatTrans.ext
  funext K
  have hK := congr_app h (J.obj K)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, Category.id_comp] at hK
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, Category.id_comp, compositeExchange_app, Functor.map_comp]
  have hn := t.hom.naturality (e.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [Category.assoc, hn, ← Category.assoc, hK]
  simp only [Category.assoc, Functor.comp_obj]

end CategoryTheory
