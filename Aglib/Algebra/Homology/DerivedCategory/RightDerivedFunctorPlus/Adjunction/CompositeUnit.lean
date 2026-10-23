/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Original unit factorization under composition of adjunctions -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Adjunction
open CategoryTheory.Functor

variable {A B C A' B' C' : Type*}
  [Category* A] [Category* B] [Category* C]
  [Category* A'] [Category* B'] [Category* C']

/-- Two actual unit-factorization equations compose without any invertibility assumption. -/
theorem unit_fac_comp
    (QA : A ⥤ A') (QB : B ⥤ B') (QC : C ⥤ C')
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : B' ⥤ C'} {R₂' : C' ⥤ B'}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (c₁ : QA ⋙ L₁' ⟶ L₁ ⋙ QB) (c₂ : QB ⋙ L₂' ⟶ L₂ ⋙ QC)
    (ρ₁ : R₁ ⋙ QA ⟶ QB ⋙ R₁') (ρ₂ : R₂ ⋙ QB ⟶ QC ⋙ R₂')
    (h₁ : ∀ X, adj₁'.unit.app (QA.obj X) ≫ R₁'.map (c₁.app X) =
      QA.map (adj₁.unit.app X) ≫ ρ₁.app (L₁.obj X))
    (h₂ : ∀ X, adj₂'.unit.app (QB.obj X) ≫ R₂'.map (c₂.app X) =
      QB.map (adj₂.unit.app X) ≫ ρ₂.app (L₂.obj X)) (X : A) :
    (adj₁'.comp adj₂').unit.app (QA.obj X) ≫
        R₁'.map (R₂'.map (L₂'.map (c₁.app X) ≫ c₂.app (L₁.obj X))) =
      QA.map ((adj₁.comp adj₂).unit.app X) ≫
        ρ₁.app (R₂.obj (L₂.obj (L₁.obj X))) ≫ R₁'.map (ρ₂.app (L₂.obj (L₁.obj X))) := by
  have hn := adj₂'.unit.naturality (c₁.app X)
  have hr := ρ₁.naturality (adj₂.unit.app (L₁.obj X))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hn hr
  have hm : adj₂'.unit.app (L₁'.obj (QA.obj X)) ≫
      R₂'.map (L₂'.map (c₁.app X) ≫ c₂.app (L₁.obj X)) =
      c₁.app X ≫ QB.map (adj₂.unit.app (L₁.obj X)) ≫
        ρ₂.app (L₂.obj (L₁.obj X)) := by
    rw [R₂'.map_comp, ← Category.assoc, ← hn, Category.assoc, h₂]
  simp only [comp_unit_app]
  rw [Category.assoc, ← R₁'.map_comp, hm, R₁'.map_comp, R₁'.map_comp,
    ← Category.assoc, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc (ρ₁.app (L₁.obj X)), ← hr, QA.map_comp]
  simp only [Category.assoc]

end CategoryTheory.Adjunction
