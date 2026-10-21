/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationFieldStep
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationCoefficientTransfer

/-!
# Artin approximation at a polynomial origin over a field

The induction hypothesis covers all finite systems over the actual
henselization in the lower dimension. The successor step first solves
polynomial-coefficient systems without using same-dimensional approximation,
then descends arbitrary henselized coefficients through their actual common
pointed-etale stage. The zero-variable case uses the original formal-map
isomorphism over a field.

This theorem concerns polynomial origins over arbitrary fields. It does not
assert the excellent-DVR case or the additional reduction from arbitrary
geometric local rings and arbitrary proper ideals to this setting.
-/

@[expose] public section

namespace PolynomialLocalHenselization

open MvPolynomial IsLocalRing

/-- The full finite-system induction, with independent numbers of equations
and unknowns and arbitrary coefficients in the actual henselization. -/
theorem exists_solution_approximation_fin (k : Type*) [Field k] (n : ℕ) :
    ∀ (s t : ℕ) (F : Fin t → MvPolynomial (Fin s) (PolynomialLocalHenselization k n))
      (y : Fin s → PolynomialLocalRing.FormalSeries k n),
      (∀ i, eval₂ (toFormalSeries k n).toRingHom y (F i) = 0) →
      ∀ c : ℕ, ∃ x : Fin s → PolynomialLocalHenselization k n,
        (∀ i, eval x (F i) = 0) ∧
        ∀ j, toFormalSeries k n (x j) - y j ∈
          maximalIdeal (PolynomialLocalRing.FormalSeries k n) ^ c := by
  induction n with
  | zero =>
      intro s t F y hy c
      obtain ⟨x, hx, hxy⟩ := exists_exact_solution_zero_variables k F y hy
      refine ⟨x, hx, fun j => ?_⟩
      rw [hxy j, sub_self]
      exact Ideal.zero_mem _
  | succ n ih =>
      intro s t F y hy c
      apply exists_solution_of_polynomial_coefficient_solver k (n + 1) ?_ F y hy c
      intro s t E b hE c
      exact exists_polynomial_coefficient_solution_of_lower_approximation k n ih E b hE c

/-- Every formal solution of a finite system over the polynomial-local
henselization at the origin over an arbitrary field has an exact henselized
solution at any prescribed maximal-adic precision. -/
theorem exists_solution_approximation (k : Type*) [Field k] (n : ℕ)
    {σ ι : Type*} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ (PolynomialLocalHenselization k n))
    (y : σ → PolynomialLocalRing.FormalSeries k n)
    (hy : ∀ i, eval₂ (toFormalSeries k n).toRingHom y (F i) = 0) (c : ℕ) :
    ∃ x : σ → PolynomialLocalHenselization k n,
      (∀ i, eval x (F i) = 0) ∧
      ∀ j, toFormalSeries k n (x j) - y j ∈
        maximalIdeal (PolynomialLocalRing.FormalSeries k n) ^ c := by
  apply exists_finite_solution_of_fin_solver (RingHom.id (PolynomialLocalHenselization k n))
    (toFormalSeries k n).toRingHom
    (maximalIdeal (PolynomialLocalRing.FormalSeries k n)) ?_ F y ?_ c
  · intro s t E b hE c
    exact exists_solution_approximation_fin k n s t E b
      (by simpa only [RingHom.comp_id] using hE) c
  · simpa only [RingHom.comp_id] using hy

end PolynomialLocalHenselization
