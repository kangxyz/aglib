/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelArrow

/-! # Original equality and family comparisons have their actual identity and cocycle laws -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS w₀ w₁ w₂
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (M₀ : ∀ C : Hom.DenseCompactification f, HasDerivedCategory.{w₀} (ModuleSheaf C.Xbar Λ))
  (M₁ : ∀ C : Hom.DenseCompactification f, HasDerivedCategory.{w₁} (ModuleSheaf C.Xbar Λ))
  (M₂ : ∀ C : Hom.DenseCompactification f, HasDerivedCategory.{w₂} (ModuleSheaf C.Xbar Λ))
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Only literally identical chosen families give the identity comparison. -/
theorem moduleExceptionalDirectImageUnboundedFamilyComparison_self :
    moduleExceptionalDirectImageUnboundedFamilyComparison f Λ hX hS M₀ M₀ N hN hΛ =
      Iso.refl _ :=
  moduleUnboundedCompactificationFamilyComparison_self f Λ hX hS M₀ N hN hΛ
    (moduleExceptionalCompactification f)

/-- The original mixed-identity cocycle gives the chosen-family cocycle. -/
theorem moduleExceptionalDirectImageUnboundedFamilyComparison_trans :
    moduleExceptionalDirectImageUnboundedFamilyComparison f Λ hX hS M₀ M₁ N hN hΛ ≪≫
      moduleExceptionalDirectImageUnboundedFamilyComparison f Λ hX hS M₁ M₂ N hN hΛ =
    moduleExceptionalDirectImageUnboundedFamilyComparison f Λ hX hS M₀ M₂ N hN hΛ := by
  apply Iso.ext
  let C := moduleExceptionalCompactification f
  have hc := @moduleUnboundedCompactificationMixedTransition_comp X S f _ Λ _ hX hS
    C C (𝟙 C) (M₂ C) (M₁ C) C (𝟙 C) (M₀ C)
  simp only [Category.id_comp] at hc
  exact hc.symm

/-- Reflexive original arrow transport with the identical family is exactly the identity. -/
theorem moduleExceptionalDirectImageUnboundedCongr_refl_self :
    moduleExceptionalDirectImageUnboundedCongr Λ hX hS (rfl : f = f) M₀ M₀ N hN hΛ =
      Iso.refl _ :=
  moduleExceptionalDirectImageUnboundedFamilyComparison_self f Λ hX hS M₀ N hN hΛ

end AlgebraicGeometry.Scheme.EtaleCohomology
