/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.FullSubcategory.Pushout

/-! The public full-subcategory pushout interface in independent universes. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

example (P : ObjectProperty D) (F : C ⥤ D) (hF : ∀ X, P (F.obj X))
    {A B E T : C} {f : A ⟶ B} {g : A ⟶ E} {i : B ⟶ T} {j : E ⟶ T}
    (h : IsPushout (F.map f) (F.map g) (F.map i) (F.map j)) :
    IsPushout ((P.lift F hF).map f) ((P.lift F hF).map g)
      ((P.lift F hF).map i) ((P.lift F hF).map j) :=
  P.isPushout_lift F hF h

example (P : ObjectProperty D) (F : C ⥤ D) (hF : ∀ X, P (F.obj X))
    {A B : C} (f : A ⟶ B) :
    P.ι.map ((P.lift F hF).map f) = F.map f := rfl
