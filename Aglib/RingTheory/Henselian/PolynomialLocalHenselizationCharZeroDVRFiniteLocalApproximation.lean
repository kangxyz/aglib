/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteLocalApproximation
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationCharZeroDVRCompletion

/-!
# Finite local approximation over a characteristic-zero DVR origin

The proved approximation theorem for the actual polynomial-origin
henselization supplies the base solver in the shared finite-local transfer.
The finite local algebra need not be flat, a domain, or of characteristic zero.
Its universe agrees with the coefficient DVR; the finite equation and unknown
types have independent universes. No solver or cofinality premise remains.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace PolynomialLocalHenselization

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]
  (n : ℕ)

local notation "H" => PolynomialLocalHenselization R n

/-- Every proper ideal of a finite local algebra over the actual
characteristic-zero DVR polynomial-origin henselization admits approximation. -/
theorem exists_solution_finite_local_ideal_completion_with_precision_of_charZeroDVR
    (A : Type u) [CommRing A] [Algebra H A] [Module.Finite H A] [IsLocalRing A]
    (I : Ideal A) (hI : I ≠ ⊤)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ A) (y : σ → AdicCompletion I A)
    (hy : ∀ i, eval₂ (algebraMap A (AdicCompletion I A)) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → A,
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (I ^ c) (x j) = AdicCompletion.evalₐ I c (y j)) ∧
      ∀ j, algebraMap A (AdicCompletion I A) (x j) - y j ∈
        (I ^ c).map (algebraMap A (AdicCompletion I A)) := by
  let : IsNoetherianRing H := Henselization.isNoetherianRing (PolynomialLocalRing R n)
  apply AdicCompletion.exists_solution_finite_local_of_solver (R := H) I hI ?_ F y hy c
  intro τ _ ε _ E t ht d
  obtain ⟨b, hb, hp, _⟩ := exists_solution_ideal_completion_with_precision_of_charZeroDVR
    R n (maximalIdeal H) (maximalIdeal.isMaximal H).ne_top E t ht d
  exact ⟨b, hb, hp⟩

end PolynomialLocalHenselization
