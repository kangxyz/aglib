/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Support containment and positive annihilating ideal powers

A finite module supported on the zero locus of a finitely generated ideal
is annihilated by a positive power of that actual ideal. No Noetherian
hypothesis is needed. Conversely, a positive annihilating power forces the
same support containment even without finiteness of the module or ideal.
-/

@[expose] public section

open PrimeSpectrum

universe u v

namespace Module

variable {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- A positive power of an ideal annihilating a module forces its native
support into the zero locus of the original ideal, without finiteness. -/
theorem support_subset_zeroLocus_of_pow_le_annihilator (I : Ideal R) {n : ℕ}
    (hn : 0 < n) (hI : I ^ n ≤ annihilator R M) :
    support R M ⊆ zeroLocus (I : Set R) := by
  rw [← zeroLocus_pow I (Nat.ne_zero_of_lt hn)]
  intro p hp
  exact hI.trans (annihilator_le_of_mem_support hp)

/-- A finitely generated ideal whose zero locus contains the native support
of a finite module has an actual positive annihilating power. -/
theorem exists_pos_pow_le_annihilator_of_support_subset [Module.Finite R M]
    (I : Ideal R) (hI : I.FG) (hM : support R M ⊆ zeroLocus (I : Set R)) :
    ∃ n : ℕ, 0 < n ∧ I ^ n ≤ annihilator R M := by
  rw [support_eq_zeroLocus] at hM
  have hr : I ≤ (annihilator R M).radical :=
    (zeroLocus_subset_zeroLocus_iff _ _).mp hM
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hr hI
  exact ⟨n + 1, Nat.succ_pos n, (Ideal.pow_le_pow_right n.le_succ).trans hn⟩

/-- Native support containment for a finite module is equivalent to an
actual positive annihilating power of the given finitely generated ideal. -/
theorem support_subset_zeroLocus_iff_exists_pos_pow_le_annihilator [Module.Finite R M]
    (I : Ideal R) (hI : I.FG) :
    support R M ⊆ zeroLocus (I : Set R) ↔
      ∃ n : ℕ, 0 < n ∧ I ^ n ≤ annihilator R M := by
  constructor
  · exact exists_pos_pow_le_annihilator_of_support_subset M I hI
  · rintro ⟨n, hn, h⟩
    exact support_subset_zeroLocus_of_pow_le_annihilator M I hn h

end Module
