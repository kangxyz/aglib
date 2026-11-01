/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelCongruence

/-! # Composition of original arrow and family transports -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS w₀ w₁ w₂
variable {X S : Scheme.{u}} {f g h : X ⟶ S}
  [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
  [CompactSpace S] [QuasiSeparatedSpace S]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  [IsSeparated h] [LocallyOfFiniteType h]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (e : f = g) (e' : g = h)
  (M₀ : ∀ C : Hom.DenseCompactification f, HasDerivedCategory.{w₀} (ModuleSheaf C.Xbar Λ))
  (M₁ : ∀ C : Hom.DenseCompactification g, HasDerivedCategory.{w₁} (ModuleSheaf C.Xbar Λ))
  (M₂ : ∀ C : Hom.DenseCompactification h, HasDerivedCategory.{w₂} (ModuleSheaf C.Xbar Λ))
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Original arrow equality and the actual mixed-identity maps obey their original cocycle. -/
theorem moduleExceptionalDirectImageUnboundedCongr_trans :
    moduleExceptionalDirectImageUnboundedCongr Λ hX hS e M₀ M₁ N hN hΛ ≪≫
      moduleExceptionalDirectImageUnboundedCongr Λ hX hS e' M₁ M₂ N hN hΛ =
    moduleExceptionalDirectImageUnboundedCongr Λ hX hS (e.trans e') M₀ M₂ N hN hΛ := by
  subst g
  subst h
  exact moduleExceptionalDirectImageUnboundedFamilyComparison_trans f Λ hX hS M₀ M₁ M₂
    N hN hΛ

end AlgebraicGeometry.Scheme.EtaleCohomology
