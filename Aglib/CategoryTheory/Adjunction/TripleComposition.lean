/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Adjunction.Triple

/-! # The original outer-adjoint comparison under composition of adjoint triples -/
@[expose] public noncomputable section
open CategoryTheory.Functor
namespace CategoryTheory.Adjunction
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {J₁ S₁ : A ⥤ B} {U₁ : B ⥤ A} {J₂ S₂ : B ⥤ C} {U₂ : C ⥤ B}
  (t₁ : Triple J₁ U₁ S₁) (t₂ : Triple J₂ U₂ S₂)

/-- Composition retains both original adjunctions of the two triples. -/
def Triple.comp : Triple (J₁ ⋙ J₂) (U₂ ⋙ U₁) (S₁ ⋙ S₂) :=
  ⟨t₁.adj₁.comp t₂.adj₁, t₂.adj₂.comp t₁.adj₂⟩

variable [J₁.Full] [J₁.Faithful] [J₂.Full] [J₂.Faithful]

/-- The canonical outer-adjoint map of the composite is the original pasted comparison. -/
theorem Triple.leftToRight_comp :
    (t₁.comp t₂).leftToRight =
      whiskerRight t₁.leftToRight J₂ ≫ whiskerLeft S₁ t₂.leftToRight := by
  ext X
  apply (cancel_mono ((S₁ ⋙ S₂).map ((t₁.comp t₂).adj₁.unit.app X))).mp
  rw [(t₁.comp t₂).leftToRight_app_map_adj₁_unit_app]
  symm
  change (J₂.map (t₁.leftToRight.app X) ≫ t₂.leftToRight.app (S₁.obj X)) ≫
      S₂.map (S₁.map ((t₁.adj₁.comp t₂.adj₁).unit.app X)) =
    (t₂.adj₂.comp t₁.adj₂).unit.app (J₂.obj (J₁.obj X))
  rw [t₂.leftToRight.naturality]
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← S₂.map_comp_assoc, t₁.leftToRight_app_map_adj₁_unit_app]
  rw [← S₂.map_comp, t₁.adj₂.unit_naturality]
  rw [S₂.map_comp, ← Category.assoc, t₂.leftToRight_app_map_adj₁_unit_app]

end CategoryTheory.Adjunction
