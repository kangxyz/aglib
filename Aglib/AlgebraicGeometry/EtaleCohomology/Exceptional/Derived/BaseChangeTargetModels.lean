/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChange
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.TargetMateModels

/-! # Original module base-change mates under independent target-model transport -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wX' wT₀ wT₁
variable (Λ : Type (u + 1)) [Ring Λ] {X S X' T : Scheme.{u}}
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (hX' : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ))
  (hT₀ : HasDerivedCategory.{wT₀} (ModuleSheaf T Λ))
  (hT₁ : HasDerivedCategory.{wT₁} (ModuleSheaf T Λ))
  (f : X ⟶ S) (f' : X' ⟶ T) (b : T ⟶ S) (a : X' ⟶ X)
  (h : f' ≫ b = a ≫ f)

/-- The actual original adjunction mate respects canonical native target comparison. -/
theorem moduleDerivedBaseChangeMap_targetModel :
    Functor.whiskerRight
        (@moduleDerivedBaseChangeMap Λ _ X S X' T hX hS hX' hT₀ f f' b a h)
        (canonicalEquivalence hT₀ hT₁).functor ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hX hX'
          (moduleInverseImage a Λ) _ _))
          (Functor.rightDerivedFunctorPlusChangeTarget hX' hT₀ hT₁
            (moduleDirectImage f' Λ)).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hX hS
          (moduleDirectImage f Λ) _ _))
          (Functor.rightDerivedFunctorPlusChangeTarget hS hT₀ hT₁
            (moduleInverseImage b Λ)).hom ≫
        @moduleDerivedBaseChangeMap Λ _ X S X' T hX hS hX' hT₁ f f' b a h :=
  rightDerivedMateModel_target hS hX hT₀ hT₁ hX'
    (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f' Λ)
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso Λ f f' b a h).hom)
    (TwoSquare.mk _ _ _ _
      (@moduleDerivedInverseImageSquareIso Λ _ X S X' T hX hS hX' hT₀ f f' b a h).hom)
    (TwoSquare.mk _ _ _ _
      (@moduleDerivedInverseImageSquareIso Λ _ X S X' T hX hS hX' hT₁ f f' b a h).hom)
    (@moduleDerivedBaseChangeMap_unit Λ _ X S X' T hX hS hX' hT₀ f f' b a h)
    (@moduleDerivedBaseChangeMap_unit Λ _ X S X' T hX hS hX' hT₁ f f' b a h)

end AlgebraicGeometry.Scheme.EtaleCohomology
