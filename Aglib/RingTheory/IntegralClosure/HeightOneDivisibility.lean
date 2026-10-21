/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.AssociatedHeight

/-! Divisibility in a normal Noetherian domain is detected in codimension one. -/

@[expose] public section

namespace IsIntegrallyClosed

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]

/-- Divisibility by a nonzero element is detected after clearing denominators outside each
height-one prime. This is the scalar codimension-one intersection theorem in divisibility form. -/
theorem dvd_of_forall_height_one {a b : R} (hb : b ≠ 0)
    (h : ∀ p : Ideal R, p.IsPrime → p.height = 1 → ∃ s ∉ p, b ∣ s * a) : b ∣ a := by
  by_contra hn
  have ha : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using hn
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (Ideal.span {b}) a) ha
  have hmem {s : R} (hs : b ∣ s * a) : s ∈ p := by
    apply hle
    rw [Submodule.mem_colon_singleton]
    change s • Ideal.Quotient.mk (Ideal.span {b}) a = 0
    simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using hs
  have hbmem : b ∈ p := hmem (dvd_mul_right b a)
  have hpne : p ≠ ⊥ := by
    intro he
    exact hb (by simpa only [he, Ideal.mem_bot] using hbmem)
  have hpheight : p.height = 1 := by
    apply le_antisymm (hp.height_le_one_of_principal hb)
    exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hpne)
  obtain ⟨s, hs, hsa⟩ := h p hp.isPrime hpheight
  exact hs (hmem hsa)

end IsIntegrallyClosed
