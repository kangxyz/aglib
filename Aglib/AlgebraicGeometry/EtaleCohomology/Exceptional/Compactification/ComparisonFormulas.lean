/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageComparison
public import Aglib.CategoryTheory.Functor.ImageCompositionAssembly

/-! # Whole factorization predicates for the original image comparisons

The original construction is unchanged. Abstract producers retain its component
formula through source restriction before any native category is substituted.
-/

@[expose] public section

namespace CategoryTheory

variable {A A' B C Z : Type*}
  [Category* A] [Category* A'] [Category* B] [Category* C] [Category* Z]
  {L₀ : A ⥤ B} {L₁ : A ⥤ C} {F : C ⥤ B}
  {R₀ : B ⥤ Z} {R₁ : C ⥤ Z}
  (δ : L₀ ⟶ L₁ ⋙ F) (e : F ⋙ R₀ ≅ R₁)

/-- The original pasted comparison has its original whole factorization predicate. -/
theorem imageComparisonFormula :
    ImageRefinementFormula δ e (imageComparison δ e) :=
  imageComparison_app δ e

/-- The unchanged original factorization survives source restriction. -/
theorem imageComparisonFormula_whiskerLeft (V : A' ⥤ A) :
    ImageRefinementFormula (L₀ := V ⋙ L₀) (L₁ := V ⋙ L₁)
      (Functor.whiskerLeft V δ) e (Functor.whiskerLeft V (imageComparison δ e)) := by
  intro K
  exact imageComparison_app δ e (V.obj K)

end CategoryTheory
