/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FittingIdeal.Minors
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Reflecting vanishing minors to the source residue field

For a local homomorphism, minors lying in the target maximal ideal already lie in the
source maximal ideal. This lets row relations be chosen and lifted on the source side.
-/

@[expose] public section

namespace Matrix

variable {R S m n : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- Vanishing of all target residual minors reflects to the source residue field. -/
theorem minorIdeal_residue_eq_bot_of_map_le_maximalIdeal (A : Matrix m n R)
    (ψ : R →+* S) [IsLocalHom ψ] (r : ℕ)
    (h : (A.map ψ).minorIdeal r ≤ IsLocalRing.maximalIdeal S) :
    (A.map (IsLocalRing.residue R)).minorIdeal r = ⊥ := by
  classical
  apply le_antisymm (Ideal.span_le.mpr ?_) bot_le
  rintro _ ⟨e, c, rfl⟩
  have htarget : ((A.map ψ).submatrix e c).det ∈ IsLocalRing.maximalIdeal S :=
    h (Ideal.subset_span ⟨e, c, rfl⟩)
  have hsource : (A.submatrix e c).det ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.maximalIdeal_comap ψ]
    change ψ (A.submatrix e c).det ∈ IsLocalRing.maximalIdeal S
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map] using htarget
  have hzero := (IsLocalRing.residue_eq_zero_iff _).mpr hsource
  change ((A.map (IsLocalRing.residue R)).submatrix e c).det = 0
  simpa only [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map] using hzero

end Matrix
