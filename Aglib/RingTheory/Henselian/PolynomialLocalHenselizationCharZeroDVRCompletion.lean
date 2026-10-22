/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationDVRCompletion
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationCharZeroDVRApproximation

/-!
# Characteristic-zero specializations of the intrinsic DVR completion

The original public interfaces are retained. Their proofs supply the canonical
completed-fraction geometric-reducedness condition and invoke the shared DVR
engine; no mathematical construction is duplicated here.
-/

@[expose] public noncomputable section

namespace PolynomialLocalHenselization

open MvPolynomial IsLocalRing

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]
  (n : ℕ)

local notation "H" => PolynomialLocalHenselization R n
local notation "Hhat" => AdicCompletion (maximalIdeal H) H

/-- Characteristic-zero approximation in the actual maximal-ideal
completion, retaining both original precision conclusions. -/
theorem exists_solution_native_completion_with_precision_of_charZeroDVR
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ H) (y : σ → Hhat)
    (hy : ∀ i, eval₂ (algebraMap H Hhat) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → H,
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (maximalIdeal H ^ c) (x j) =
        AdicCompletion.evalₐ (maximalIdeal H) c (y j)) ∧
      ∀ j, algebraMap H Hhat (x j) - y j ∈
        (maximalIdeal H ^ c).map (algebraMap H Hhat) := by
  exact exists_solution_native_completion_with_precision_of_geometricallyReducedFractionCompletion
    R n (AdicCompletion.hasGeometricallyReducedFractionCompletion_of_charZero R) F y hy c

/-- Characteristic-zero approximation in every original proper-ideal
completion, retaining both original precision conclusions. -/
theorem exists_solution_ideal_completion_with_precision_of_charZeroDVR
    (I : Ideal H) (hI : I ≠ ⊤)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ H) (y : σ → AdicCompletion I H)
    (hy : ∀ i, eval₂ (algebraMap H (AdicCompletion I H)) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → H,
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (I ^ c) (x j) = AdicCompletion.evalₐ I c (y j)) ∧
      ∀ j, algebraMap H (AdicCompletion I H) (x j) - y j ∈
        (I ^ c).map (algebraMap H (AdicCompletion I H)) := by
  exact exists_solution_ideal_completion_with_precision_of_geometricallyReducedFractionCompletion
    R n (AdicCompletion.hasGeometricallyReducedFractionCompletion_of_charZero R) I hI F y hy c

end PolynomialLocalHenselization
