/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenBaseChangeConjugacy
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianExchangeMate
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.IsomorphismComparison

/-! # The independently derived Cartesian exchange is the original base-change map -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wV wU wY wX

variable {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [Etale i] [Etale j] (h : IsPullback g i j f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

local instance : (moduleInverseImage i Λ).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (moduleLowerShriekAdjunction i Λ)

/-- The transported Cartesian right exchange is the same original derived adjunction mate. -/
theorem moduleDerivedCartesianExchangeIso_hom :
    (moduleDerivedCartesianExchangeIso g i j f h Λ).hom =
      moduleDerivedBaseChangeMap Λ f g j i h.w := by
  exact (derivedMate_eq_derivedIso
    (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction g Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f g j i h.w).hom)
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageSquareIso Λ f g j i h.w).hom)
    (moduleDerivedInverseImageSquareIso_exactComparison Λ f g j i h.w)
    (moduleCartesianExchangeIso g i j f h Λ)
    (moduleCartesianExchangeIso_hom g i j f h Λ)).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
