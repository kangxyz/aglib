/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.ApproximationTransfer
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationNativeApproximation
public import Aglib.RingTheory.Henselian.HenselizationNoetherian

/-! # Arbitrary-ideal Artin approximation at a polynomial origin

The ideal completion and its quotient projections are the native ones. The
maximal-adic theorem is used only to solve the affine-substituted exact system.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace PolynomialLocalHenselization

universe u v w
variable (k : Type u) [Field k] (n : ℕ)

local notation "H" => PolynomialLocalHenselization k n

/-- Approximation for any proper ideal in the actual henselization of a
polynomial origin over an arbitrary field. Both the original finite quotient
projection and the original completed-ring ideal precision are retained. -/
theorem exists_solution_ideal_completion_with_precision
    (I : Ideal H) (hI : I ≠ ⊤)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ H) (y : σ → AdicCompletion I H)
    (hy : ∀ i, eval₂ (algebraMap H (AdicCompletion I H)) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → H,
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (I ^ c) (x j) = AdicCompletion.evalₐ I c (y j)) ∧
      ∀ j, algebraMap H (AdicCompletion I H) (x j) - y j ∈
        (I ^ c).map (algebraMap H (AdicCompletion I H)) := by
  let : IsNoetherianRing H := Henselization.isNoetherianRing (PolynomialLocalRing k n)
  apply AdicCompletion.exists_solution_of_larger_ideal_solver I (maximalIdeal H)
    (le_maximalIdeal hI) (IsNoetherian.noetherian I) ?_ F y hy c
  intro τ _ E z hz
  obtain ⟨x, hx, _⟩ := exists_solution_native_completion k n E z hz 0
  exact ⟨x, hx⟩

end PolynomialLocalHenselization
