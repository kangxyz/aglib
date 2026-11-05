/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange

/-! # The original module-derived exchange at the original single

A typed name retains the literal original exchange component and all four
original derived-category choices, without expanding its mate construction
inside later higher-image comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wS wX' wS'

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
    [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)

/-- The actual original exchange component with explicit native source and target. -/
def moduleDerivedBaseChangeSingleComponent (F : ModuleSheaf X Λ) :
    (moduleDerivedInverseImage Λ g).obj ((moduleDerivedDirectImage Λ f).obj
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj F)) ⟶
    (moduleDerivedDirectImage Λ f').obj ((moduleDerivedInverseImage Λ g').obj
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj F)) :=
  (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app
    ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj F)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
