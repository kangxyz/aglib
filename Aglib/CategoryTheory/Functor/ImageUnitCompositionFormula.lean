/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageUnitHorizontal
public import Aglib.CategoryTheory.Functor.ImageCompositionAssembly

/-! # Whole original composition formulas as unit-image formulas -/

@[expose] public section
namespace CategoryTheory
variable {A B B' C C' Z : Type*}
  [Category* A] [Category* B] [Category* B'] [Category* C] [Category* C'] [Category* Z]
  {J' : A ⥤ B'} {L : B ⥤ C} {L' : B' ⥤ C'} {T' : A ⥤ C'}
  {R : B' ⥤ B} {S : C' ⥤ C} {P : C ⥤ Z} {P' : C' ⥤ Z}

/-- Keep the accepted original formula whole while changing only
the named compositor orientation. -/
theorem imageUnitHorizontalFormula_of_composition
    (σ : R ⋙ L ⟶ L' ⋙ S) (c : J' ⋙ L' ≅ T') (c' : T' ≅ J' ⋙ L')
    (e : S ⋙ P ≅ P') (α : J' ⋙ R ⋙ L ⋙ P ⟶ T' ⋙ P')
    (hc : c = c'.symm) (h : ImageCompositionFormula σ c e α) :
    ImageUnitHorizontalFormula σ c' e α := by
  subst c
  exact h

end CategoryTheory
