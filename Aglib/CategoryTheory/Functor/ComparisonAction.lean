/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Scalar squares through the original whiskered comparison

Compose two actual natural-transformation squares before specializing any
geometric categories. All associators and comparisons remain the original maps.
-/

@[expose] public section
open CategoryTheory
namespace CategoryTheory.Functor
universe uA vA uB vB uC vC uD vD uE vE
variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E]
  (I : A ⥤ B) (F : B ⥤ C) (U : C ⥤ E) (V : B ⥤ D) (H : D ⥤ E)
  (J : A ⥤ D) (e : F ⋙ U ≅ V ⋙ H) (c : I ⋙ V ≅ J)

/-- The original associator/whiskering comparison, with one shared definition head. -/
def whiskeredComparison : (I ⋙ F) ⋙ U ≅ J ⋙ H :=
  associator I F U ≪≫ isoWhiskerLeft I e ≪≫
    (associator I V H).symm ≪≫ isoWhiskerRight c H

/-- The original composed comparison carries the two given action squares. -/
theorem whiskeredComparison_action
    (α : U ⟶ U) (β : V ⟶ V) (γ : J ⟶ J)
    (he : whiskerLeft F α ≫ e.hom = e.hom ≫ whiskerRight β H)
    (hc : whiskerLeft I β ≫ c.hom = c.hom ≫ γ) :
    whiskerLeft (I ⋙ F) α ≫
        (whiskeredComparison I F U V H J e c).hom =
      (whiskeredComparison I F U V H J e c).hom ≫
        whiskerRight γ H := by
  ext X
  have h₁ := NatTrans.congr_app he (I.obj X)
  have h₂ := congrArg H.map (NatTrans.congr_app hc X)
  change α.app (F.obj (I.obj X)) ≫ e.hom.app (I.obj X) =
    e.hom.app (I.obj X) ≫ H.map (β.app (I.obj X)) at h₁
  change H.map (β.app (I.obj X) ≫ c.hom.app X) =
    H.map (c.hom.app X ≫ γ.app X) at h₂
  rw [H.map_comp, H.map_comp] at h₂
  have h : α.app (F.obj (I.obj X)) ≫ e.hom.app (I.obj X) ≫ H.map (c.hom.app X) =
      e.hom.app (I.obj X) ≫ H.map (c.hom.app X) ≫ H.map (γ.app X) := by
    rw [← Category.assoc, h₁, Category.assoc, h₂]
  simpa [whiskeredComparison] using h

end CategoryTheory.Functor
