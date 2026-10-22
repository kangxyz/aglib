/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationDVRReduction

/-!
# Characteristic-zero specializations of the intrinsic DVR reduction

The original public interfaces are retained. Their proofs supply the canonical
completed-fraction geometric-reducedness condition and invoke the shared DVR
engine; no mathematical construction is duplicated here.
-/

@[expose] public noncomputable section

namespace PolynomialLocalHenselization

open MvPolynomial IsLocalRing

universe u
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]
  (n : ℕ)

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "P" => MvPolynomial (Fin n) R
local notation "C" => PolynomialLocalRing.FormalSeries R n
local notation "H" => PolynomialLocalHenselization R n

/-- The original characteristic-zero selected-system reduction, supplied by
the shared intrinsic completed-fraction construction. -/
theorem exists_selected_system_at_formal_point_of_charZeroDVR
    (m t : ℕ) (F : Fin t → MvPolynomial (Fin m) P) (y : Fin m → C)
    (hy : ∀ i, eval₂ (PolynomialLocalRing.polynomialToFormalSeries R n).toRingHom
      y (F i) = 0) (c : ℕ) :
    ∃ (ℓ : ℕ) (z : Fin m ⊕ Fin ℓ → C) (r : ℕ)
      (G : Fin r → MvPolynomial (Fin m ⊕ Fin ℓ) P)
      (cols : Fin r ↪ Fin m ⊕ Fin ℓ) (N : ℕ),
      (∀ j, z (Sum.inl j) = y j) ∧ c ≤ N ∧
      (∀ j, eval₂ (PolynomialLocalRing.polynomialToFormalSeries R n).toRingHom
        z (G j) = 0) ∧
      MvPowerSeries.map (residue Rhat)
        (eval₂ (PolynomialLocalRing.polynomialToFormalSeries R n).toRingHom z
          (Matrix.det (Matrix.of fun i j => pderiv (cols j) (G i)))) ≠ 0 ∧
      ∀ x : Fin m ⊕ Fin ℓ → H,
        (∀ j, toFormalSeries R n (x j) - z j ∈ maximalIdeal C ^ N) →
        (∀ j, eval₂ (polynomialToHenselization R n).toRingHom x (G j) = 0) →
        ∀ i, eval₂ (polynomialToHenselization R n).toRingHom
          (fun j => x (Sum.inl j)) (F i) = 0 := by
  exact exists_selected_system_at_formal_point_of_geometricallyReducedFractionCompletion
    R n (AdicCompletion.hasGeometricallyReducedFractionCompletion_of_charZero R) m t F y hy c

end PolynomialLocalHenselization
