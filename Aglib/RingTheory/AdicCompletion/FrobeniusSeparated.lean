/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Separatedness under a bounded Frobenius exponent

An injective algebra map from an adically separated ring to a reduced algebra
preserves separatedness if one fixed Frobenius power of every algebra element
belongs to the actual image of the coefficient ring. The module action throughout
is the original algebra action.
-/

@[expose] public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal R) (p e : ℕ) [ExpChar S p]

/-- A fixed Frobenius power sends every finite sum in `I ^ n • S` into the
actual coefficient image of `I ^ (n * p ^ e)`. -/
theorem exists_mem_pow_algebraMap_eq_pow_of_mem_smul_top
    (hpow : ∀ s : S, ∃ r : R, algebraMap R S r = s ^ (p ^ e))
    (n : ℕ) {s : S} (hs : s ∈ (I ^ n) • (⊤ : Submodule R S)) :
    ∃ r ∈ I ^ (n * p ^ e), algebraMap R S r = s ^ (p ^ e) := by
  refine Submodule.smul_induction_on hs ?_ ?_
  · intro r hr s _
    obtain ⟨t, ht⟩ := hpow s
    refine ⟨r ^ (p ^ e) * t, ?_, ?_⟩
    · apply (I ^ (n * p ^ e)).mul_mem_right
      simpa only [pow_mul] using Ideal.pow_mem_pow hr (p ^ e)
    · rw [map_mul, map_pow, ht, Algebra.smul_def, mul_pow]
  · intro s t hs ht
    obtain ⟨r, hr, hrs⟩ := hs
    obtain ⟨u, hu, hut⟩ := ht
    refine ⟨r + u, (I ^ (n * p ^ e)).add_mem hr hu, ?_⟩
    rw [map_add, hrs, hut]
    exact ((iterateFrobenius S p e).map_add s t).symm

end Ideal

namespace IsHausdorff

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal R) (p e : ℕ) [ExpChar S p]

/-- Separatedness ascends through an injective algebra map into a reduced
algebra when a fixed Frobenius power has image in the coefficient ring.
The conclusion uses the original `R`-module action on `S`. -/
theorem of_frobenius_pow_mem_range [IsHausdorff I R] [IsReduced S]
    (hinj : Function.Injective (algebraMap R S))
    (hpow : ∀ s : S, ∃ r : R, algebraMap R S r = s ^ (p ^ e)) :
    IsHausdorff I S := by
  refine ⟨fun s hs ↦ ?_⟩
  obtain ⟨r, hr⟩ := hpow s
  have hr0 : r = 0 := by
    apply IsHausdorff.haus (inferInstance : IsHausdorff I R) r
    intro n
    obtain ⟨t, ht, hts⟩ :=
      I.exists_mem_pow_algebraMap_eq_pow_of_mem_smul_top p e hpow n
        (SModEq.zero.mp (hs n))
    have hrt : r = t := hinj (hr.trans hts.symm)
    have hrmem : r ∈ I ^ n := by
      rw [hrt]
      exact Ideal.pow_le_pow_right
        (Nat.le_mul_of_pos_right n (expChar_pow_pos S p e)) ht
    apply SModEq.zero.mpr
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hrmem
  apply eq_zero_of_pow_eq_zero (n := p ^ e)
  rw [← hr, hr0, map_zero]

end IsHausdorff
