/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# A DVR fraction field by inverting one nonunit

Every nonzero nonunit is a valid denominator generator. This includes ramified images of
uniformizers from a smaller DVR, not only uniformizers of the target ring.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Any nonzero element divides a power of any fixed nonzero nonunit. -/
theorem exists_dvd_pow_of_nonzero_nonunit {c : R} (hc : c ≠ 0) (hcu : ¬ IsUnit c)
    {x : R} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ c ^ n := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨e, he⟩ := associated_pow_irreducible hc hπ
  obtain ⟨n, hn⟩ := associated_pow_irreducible hx hπ
  have hepos : 0 < e := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hcu
    apply he.isUnit_iff.mpr
    simp [hz]
  refine ⟨n, hn.dvd.trans ((pow_dvd_pow π (Nat.le_mul_of_pos_left n hepos)).trans ?_)⟩
  simpa only [pow_mul] using (he.pow_pow (n := n)).symm.dvd

/-- A fraction field of a DVR is the actual localization at any nonzero nonunit. -/
theorem isLocalizationAway_of_nonzero_nonunit (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] {c : R} (hc : c ≠ 0) (hcu : ¬ IsUnit c) :
    IsLocalization.Away c K := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (S := K) (Submonoid.powers c)
    (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hc) ?_).mpr
      (inferInstance : IsLocalization (nonZeroDivisors R) K)
  intro x hx
  obtain ⟨n, hn⟩ := exists_dvd_pow_of_nonzero_nonunit hc hcu
    ((mem_nonZeroDivisors_iff_ne_zero).mp hx)
  exact ⟨c ^ n, ⟨n, rfl⟩, hn⟩

end IsDiscreteValuationRing
