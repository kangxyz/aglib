/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.HenselianPrincipalRoots
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Unit roots with prescribed residue

A residue root of a unit lifts to a unit root for an invertible positive
exponent in a Henselian local ring. The complete principal-unit construction
is reused after dividing by the power of a lift. A separably closed residue
field supplies the residue root; no completeness or perfectness is required.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace HenselianLocalRing

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- Lift a specified residue root, preserving its value and the original unit equation. -/
theorem exists_unit_root_with_residue
    (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (u : Rˣ) (c : ResidueField R) (hc : c ^ n = residue R (u : R)) :
    ∃ v : Rˣ, residue R (v : R) = c ∧ v ^ n = u := by
  have hc0 : c ≠ 0 := by
    intro h
    have hu := (u.isUnit.map (residue R)).ne_zero
    apply hu
    rw [← hc, h, zero_pow (Nat.ne_of_gt hn)]
  obtain ⟨a, ha⟩ := residue_surjective (R := R) c
  have hau : IsUnit a := (residue_ne_zero_iff_isUnit a).mp (by rwa [ha])
  obtain ⟨a, rfl⟩ := hau
  let w : Rˣ := u * (a ^ n)⁻¹
  have hw : residue R (w : R) = 1 := by
    simp [w, ha, ← hc, hc0]
  obtain ⟨v, hv, hvpow⟩ := PrincipalRoots.exists_pow_eq n hn hnunit w hw
  refine ⟨a * v, ?_, ?_⟩
  · simp only [Units.val_mul, map_mul, ha, hv, mul_one]
  · rw [mul_pow, hvpow]
    simp [w]

/-- Every unit has an `n`-th root over a Henselian local ring with separably
closed residue field, for a positive invertible exponent. -/
theorem exists_unit_pow_eq_of_isSepClosed_residue
    [IsSepClosed (ResidueField R)]
    (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R)) (u : Rˣ) :
    ∃ v : Rˣ, v ^ n = u := by
  let : NeZero (n : ResidueField R) := ⟨by
    simpa only [map_natCast] using (hnunit.map (residue R)).ne_zero⟩
  obtain ⟨c, hc⟩ := IsSepClosed.exists_pow_nat_eq (residue R (u : R)) n
  obtain ⟨v, _, hv⟩ := exists_unit_root_with_residue n hn hnunit u c hc
  exact ⟨v, hv⟩

end HenselianLocalRing
