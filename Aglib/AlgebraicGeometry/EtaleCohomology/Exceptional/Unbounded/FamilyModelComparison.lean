/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.MixedModelTransition

/-! # Original identity-refinement comparisons between independent model families -/

@[expose] public noncomputable section

open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM₀ wM₁
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (M₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ))
  (M₁ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ))
  (C : Hom.DenseCompactification f)
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The actual mixed identity refinement, not an identification of model instances. -/
def moduleUnboundedCompositionFamilyComparison :
    (@moduleUnboundedCompactificationFunctor X S f Λ _ hX hS C (M₀ C)) ≅
      (@moduleUnboundedCompactificationFunctor X S f Λ _ hX hS C (M₁ C)) := by
  exact @asIso _ _ _ _
    (@moduleUnboundedCompactificationMixedTransition X S f _ Λ _ hX hS
      C C (𝟙 C) (M₁ C) (M₀ C))
    (@moduleUnboundedCompactificationMixedTransition_isIso X S f _ Λ _ hX hS
      C C (𝟙 C) (M₁ C) (M₀ C) N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
