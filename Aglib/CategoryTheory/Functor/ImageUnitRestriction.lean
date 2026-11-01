/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageUnitHorizontal

/-! # Whole source restriction of original unit faces -/

@[expose] public section
namespace CategoryTheory
variable {A A₀ B B' C C' : Type*}
  [Category* A] [Category* A₀] [Category* B] [Category* B'] [Category* C] [Category* C']
  {J : A ⥤ B} {J' : A ⥤ B'} {L : B ⥤ C} {L' : B' ⥤ C'}
  {T : A ⥤ C} {T' : A ⥤ C'} {R : B' ⥤ B} {S : C' ⥤ C}

/-- Restrict an already proved original horizontal unit face before concrete specialization. -/
theorem unitMateHorizontalEquation_whiskerLeft (V : A₀ ⥤ A)
    (δJ : J ⟶ J' ⋙ R) (δT : T ⟶ T' ⋙ S)
    (σ : R ⋙ L ⟶ L' ⋙ S) (c : T ≅ J ⋙ L) (c' : T' ≅ J' ⋙ L')
    (h : UnitMateHorizontalEquation δJ δT σ c c') :
    UnitMateHorizontalEquation
      (J := V ⋙ J) (J' := V ⋙ J') (T := V ⋙ T) (T' := V ⋙ T')
      (L := L) (L' := L') (R := R) (S := S)
      (Functor.whiskerLeft V δJ) (Functor.whiskerLeft V δT) σ
      (Functor.isoWhiskerLeft V c) (Functor.isoWhiskerLeft V c') := by
  intro K
  exact h (V.obj K)

end CategoryTheory
