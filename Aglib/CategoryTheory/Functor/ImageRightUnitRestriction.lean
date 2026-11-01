/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageRightUnit

/-! # Whole source restriction of original right-unit open faces -/

@[expose] public section
namespace CategoryTheory
variable {U U₀ A B : Type*} [Category* U] [Category* U₀] [Category* A] [Category* B]
  {J : U ⥤ A} {L : U ⥤ B} {M N : A ⥤ B}

/-- Restriction retains the supplied original compositor after its proved identification. -/
theorem rightUnitOpenEquation_whiskerLeft_of_eq (V : U₀ ⥤ U)
    (c₀ c : J ⋙ M ≅ L) (δ : L ⟶ J ⋙ N) (b : M ⟶ N)
    (hc : c₀ = c) (h : RightUnitOpenEquation c₀ δ b) :
    RightUnitOpenEquation (J := V ⋙ J) (L := V ⋙ L)
      (Functor.isoWhiskerLeft V c) (Functor.whiskerLeft V δ) b := by
  subst c
  intro K
  exact h (V.obj K)

end CategoryTheory
