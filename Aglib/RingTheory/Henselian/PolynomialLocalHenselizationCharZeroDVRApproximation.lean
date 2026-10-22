/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationDVRApproximation
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationCharZeroDVRReduction

/-!
# Characteristic-zero specializations of the intrinsic DVR approximation

The original public interfaces are retained. Their proofs supply the canonical
completed-fraction geometric-reducedness condition and invoke the shared DVR
engine; no mathematical construction is duplicated here.
-/

@[expose] public noncomputable section

namespace PolynomialLocalHenselization

open MvPolynomial IsLocalRing

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]

/-- Full finite-system characteristic-zero approximation at the original
maximal-adic formal-series precision. -/
theorem exists_solution_approximation_fin_of_charZeroDVR (n : ℕ) :
    ∀ (s t : ℕ) (F : Fin t → MvPolynomial (Fin s) (PolynomialLocalHenselization R n))
      (y : Fin s → PolynomialLocalRing.FormalSeries R n),
      (∀ i, eval₂ (toFormalSeries R n).toRingHom y (F i) = 0) →
      ∀ c : ℕ, ∃ x : Fin s → PolynomialLocalHenselization R n,
        (∀ i, eval x (F i) = 0) ∧
        ∀ j, toFormalSeries R n (x j) - y j ∈
          maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c := by
  exact exists_solution_approximation_fin_of_geometricallyReducedFractionCompletion
    R n (AdicCompletion.hasGeometricallyReducedFractionCompletion_of_charZero R)

/-- Characteristic-zero formal-series approximation with independent finite
equation and unknown universes. -/
theorem exists_solution_approximation_of_charZeroDVR (n : ℕ)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ (PolynomialLocalHenselization R n))
    (y : σ → PolynomialLocalRing.FormalSeries R n)
    (hy : ∀ i, eval₂ (toFormalSeries R n).toRingHom y (F i) = 0) (c : ℕ) :
    ∃ x : σ → PolynomialLocalHenselization R n,
      (∀ i, eval x (F i) = 0) ∧
      ∀ j, toFormalSeries R n (x j) - y j ∈
        maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c := by
  exact exists_solution_approximation_of_geometricallyReducedFractionCompletion
    R n (AdicCompletion.hasGeometricallyReducedFractionCompletion_of_charZero R) F y hy c

end PolynomialLocalHenselization
