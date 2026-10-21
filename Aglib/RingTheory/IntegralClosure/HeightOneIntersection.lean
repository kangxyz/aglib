/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.HeightOneDivisibility

/-! Scalar intersection inside the actual fraction field of a normal Noetherian domain. -/

@[expose] public section

namespace IsIntegrallyClosed

variable {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- A fraction whose denominator can be cleared outside every height-one prime belongs to
its normal Noetherian base ring. -/
theorem mem_range_of_forall_height_one {x : K}
    (h : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      ∃ s ∉ p, x * algebraMap R K s ∈ Set.range (algebraMap R K)) :
    x ∈ Set.range (algebraMap R K) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbK : algebraMap R K b ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hb0
  have hd : b ∣ a := dvd_of_forall_height_one hb0 fun p hp hh ↦ by
    obtain ⟨s, hs, t, ht⟩ := h p hp hh
    refine ⟨s, hs, t, (IsFractionRing.injective R K) ?_⟩
    rw [div_mul_eq_mul_div] at ht
    have he := (eq_div_iff hbK).mp ht
    simpa only [map_mul, mul_comm] using he.symm
  obtain ⟨t, ht⟩ := hd
  refine ⟨t, ?_⟩
  apply (eq_div_iff hbK).mpr
  simp only [ht, map_mul, mul_comm]

end IsIntegrallyClosed
