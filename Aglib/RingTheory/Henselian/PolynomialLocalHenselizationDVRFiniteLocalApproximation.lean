/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteLocalApproximation
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationDVRCompletion

/-!
# Finite local approximation under the intrinsic DVR condition

The intrinsic polynomial-origin theorem supplies the solver to the shared
finite-local transfer. No characteristic assumption on the coefficient ring or
finite local algebra is required. Both original precision conditions remain.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace PolynomialLocalHenselization

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (n : ℕ)

local notation "H" => PolynomialLocalHenselization R n

/-- Approximation for every proper ideal of a finite local algebra over the
actual polynomial-origin henselization under the intrinsic DVR condition. -/
theorem
    exists_solution_finite_local_ideal_completion_with_precision_of_fractionCompletion
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R)
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
  obtain ⟨b, hb, hp, _⟩ :=
    exists_solution_ideal_completion_with_precision_of_geometricallyReducedFractionCompletion
      R n hcoeff (maximalIdeal H) (maximalIdeal.isMaximal H).ne_top E t ht d
  exact ⟨b, hb, hp⟩

end PolynomialLocalHenselization
