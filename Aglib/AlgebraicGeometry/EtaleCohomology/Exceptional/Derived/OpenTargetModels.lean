/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenTripleComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetNatTrans

/-! # The original canonical open comparison respects independent native target models -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dU dX₀ dX₁
variable (Λ : Type (u + 1)) [Ring Λ] {U X : Scheme.{u}}
  (j : U ⟶ X) [IsOpenImmersion j]
  (hU : HasDerivedCategory.{dU} (ModuleSheaf U Λ))
  (hX₀ : HasDerivedCategory.{dX₀} (ModuleSheaf X Λ))
  (hX₁ : HasDerivedCategory.{dX₁} (ModuleSheaf X Λ))

/-- The actual canonical triple map, not a replacement derived map, preserves target transport. -/
theorem moduleDerivedLowerShriekToDirectImage_target :
    DerivedModelNatTransTargetEquation hU hX₀ hX₁
      (moduleLowerShriek j Λ) (moduleDirectImage j Λ)
      (@moduleDerivedLowerShriekToDirectImage Λ _ U X j _ hU hX₀)
      (@moduleDerivedLowerShriekToDirectImage Λ _ U X j _ hU hX₁) :=
  rightDerivedFunctorPlusChangeTarget_natTrans hU hX₀ hX₁
    (moduleLowerShriek j Λ) (moduleDirectImage j Λ) (moduleLowerShriekToDirectImage Λ j)
    (@moduleDerivedLowerShriekToDirectImage Λ _ U X j _ hU hX₀)
    (@moduleDerivedLowerShriekToDirectImage Λ _ U X j _ hU hX₁)
    (moduleDerivedLowerShriekToDirectImage_unit Λ j hU hX₀)
    (moduleDerivedLowerShriekToDirectImage_unit Λ j hU hX₁)

end AlgebraicGeometry.Scheme.EtaleCohomology
