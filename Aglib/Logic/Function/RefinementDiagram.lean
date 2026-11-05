/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Logic.Function.Basic

/-! # Evaluation through original refinement comparison diagrams

The complete function calculation is independent of categorical carriers and
cohomology dictionaries. Applications supply the actual naturality, square and
composition laws for their original functions.
-/

@[expose] public section
namespace Function

/-- Naturality with an invertible source comparison cancels its actual inverse. -/
theorem comparison_cancel
    {A B C D : Type*} (γ : A → B) (γinv : B → A)
    (s : A → C) (s' : B → D) (δ : C → D)
    (hγ : ∀ y, γ (γinv y) = y)
    (hn : ∀ x, δ (s x) = s' (γ x)) (y : B) :
    δ (s (γinv y)) = s' y :=
  (hn (γinv y)).trans (congrArg s' (hγ y))

/-- Complete evaluation of a normalized refined class through its original
coefficient square, original pullback square and coefficient naturality. -/
theorem refinement_diagram_apply
    {A₀ A₁ A₂ B₀ B₁ B₂ B₃ C₀ C₁ C₂ : Type*}
    (r : A₀ → A₁) (normalize : A₁ → A₂)
    (s : A₂ → B₁) (denormalize : B₁ → B₂) (sNested : A₁ → B₂)
    (square : B₂ → B₃) (oldRestriction : A₀ → B₀) (rClosed : B₀ → B₃)
    (oldCoefficient : B₀ → C₀) (rCoefficient : C₀ → C₂)
    (newCoefficient : B₁ → C₁) (targetComparison : C₁ → C₂)
    (pulledCoefficient : B₃ → C₂)
    (hcancel : ∀ y, denormalize (s (normalize y)) = sNested y)
    (hsquare : ∀ x, square (sNested (r x)) = rClosed (oldRestriction x))
    (hcoefficient : ∀ z, targetComparison (newCoefficient z) =
      pulledCoefficient (square (denormalize z)))
    (hnaturality : ∀ z, pulledCoefficient (rClosed z) = rCoefficient (oldCoefficient z))
    (x : A₀) :
    targetComparison (newCoefficient (s (normalize (r x)))) =
      rCoefficient (oldCoefficient (oldRestriction x)) := by
  rw [hcoefficient, hcancel, hsquare, hnaturality]

end Function
