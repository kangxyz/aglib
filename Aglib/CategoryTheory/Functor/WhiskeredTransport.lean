/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Invertibility through an actual whiskered transport equation

The specified comparison isomorphisms preserve and reflect invertibility of
its mapped middle component. No reflection property of the final functor is
required: the conclusion concerns its image of the original component.
-/

@[expose] public section

namespace CategoryTheory

universe a₁ a₂ a₃ a₄ v₁ v₂ v₃ v₄

variable {A : Type a₁} [Category.{v₁} A] {B : Type a₂} [Category.{v₂} B]
  {C : Type a₃} [Category.{v₃} C] {D : Type a₄} [Category.{v₄} D]
  {J : A ⥤ B} {L M : B ⥤ C} {H : C ⥤ D} {U V : A ⥤ D}

/-- Cancel only the two actual comparison isomorphisms in the complete
whiskered transport equation. The middle arrow remains mapped by `H`. -/
theorem isIso_app_iff_of_whiskered_transport
    (s : U ≅ J ⋙ L ⋙ H) (β : L ⟶ M) (t : J ⋙ M ⋙ H ≅ V)
    (δ : U ⟶ V)
    (hδ : δ = s.hom ≫ Functor.whiskerLeft J (Functor.whiskerRight β H) ≫ t.hom)
    (X : A) : IsIso (δ.app X) ↔ IsIso (H.map (β.app (J.obj X))) := by
  rw [hδ]
  change IsIso (s.hom.app X ≫ H.map (β.app (J.obj X)) ≫ t.hom.app X) ↔
    IsIso (H.map (β.app (J.obj X)))
  exact (isIso_comp_left_iff _ _).trans (isIso_comp_right_iff _ _)

end CategoryTheory
