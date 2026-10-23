/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Reducedness from associated-prime localizations

Vanishing in the original ring localizations at the associated primes of a
quotient detects membership in its ideal. A regular element and separatedness
then turn reducedness at the associated localizations of its principal
quotient into reducedness of the original ring.

A separate local statement identifies a reduced quotient with the residue
field when the maximal ideal is associated to that quotient module. This
statement uses the radical-annihilator witness and needs no Noetherianity.
-/

@[expose] public section

/-- Vanishing in the ring localizations at the associated primes of an
actual quotient detects membership in the original ideal. -/
theorem Ideal.mem_of_zero_at_associated_localizations
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (z : A)
    (hz : ∀ (p : Ideal A) [p.IsPrime], IsAssociatedPrime p (A ⧸ I) →
      algebraMap A (Localization.AtPrime p) z = 0) : z ∈ I := by
  by_contra hzI
  have hz0 : Ideal.Quotient.mk I z ≠ 0 := by
    intro hzero
    exact hzI (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  obtain ⟨p, hp, hann⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing A (Ideal.Quotient.mk I z) hz0
  let : p.IsPrime := hp.isPrime
  obtain ⟨s, hs⟩ :=
    (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) z).mp (hz p hp)
  have hsmul : (s : A) • Ideal.Quotient.mk I z = 0 := by
    change Ideal.Quotient.mk I ((s : A) * z) = 0
    rw [hs, map_zero]
  apply (Ideal.mem_primeCompl_iff.mp s.2)
  apply hann
  simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using hsmul

/-- A Noetherian ring separated for a regular principal ideal is reduced
if its ambient localizations at the associated primes of that principal
quotient are reduced. No domain or completeness hypothesis is used. -/
theorem IsReduced.of_isHausdorff_of_associated_localizations
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A)
    [IsHausdorff (Ideal.span {x}) A]
    (hloc : ∀ (p : Ideal A) [p.IsPrime],
      IsAssociatedPrime p (A ⧸ Ideal.span {x}) → IsReduced (Localization.AtPrime p)) :
    IsReduced A := by
  have hdiv : ∀ z : A, z ^ 2 = 0 → ∃ y : A, z = x * y ∧ y ^ 2 = 0 := by
    intro z hz
    have hmem : z ∈ Ideal.span {x} := by
      apply Ideal.mem_of_zero_at_associated_localizations
      intro p hp hass
      let : IsReduced (Localization.AtPrime p) := hloc p hass
      apply IsReduced.eq_zero
      refine ⟨2, ?_⟩
      rw [← map_pow, hz, map_zero]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hmem
    refine ⟨y, hy, ?_⟩
    apply (mem_nonZeroDivisors_iff_left.mp (pow_mem hx 2)) (y ^ 2)
    rw [← mul_pow, ← hy]
    exact hz
  apply (isReduced_iff_pow_one_lt 2 (by decide)).mpr
  intro z hz
  have hpow : ∀ n : ℕ, ∃ y : A, z = x ^ n * y ∧ y ^ 2 = 0 := by
    intro n
    induction n with
    | zero => exact ⟨z, by simp, hz⟩
    | succ n ih =>
      obtain ⟨y, hy, hyzero⟩ := ih
      obtain ⟨w, hw, hwzero⟩ := hdiv y hyzero
      refine ⟨w, ?_, hwzero⟩
      rw [hy, hw, pow_succ, mul_assoc]
  apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {x}) A) z
  intro n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨y, hy, _⟩ := hpow n
  exact Ideal.mem_span_singleton.mpr ⟨y, hy⟩

/-- In a local ring, a reduced quotient whose module has associated
maximal ideal is the residue-field quotient. The radical-annihilator
witness suffices, without a Noetherianity hypothesis. -/
theorem Ideal.eq_maximalIdeal_of_isReduced_quotient_of_isAssociatedPrime
    {A : Type*} [CommRing A] [IsLocalRing A] (I : Ideal A)
    [IsReduced (A ⧸ I)]
    (h : IsAssociatedPrime (IsLocalRing.maximalIdeal A) (A ⧸ I)) :
    I = IsLocalRing.maximalIdeal A := by
  obtain ⟨u, hu⟩ := h.2
  have hu0 : u ≠ 0 := by
    intro hzero
    apply h.isPrime.ne_top
    rw [hzero, Submodule.colon_singleton_zero, Ideal.radical_top] at hu
    exact hu
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
  have haunit : IsUnit a := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro ha
    rw [hu, Ideal.mem_radical_iff] at ha
    obtain ⟨n, hn⟩ := ha
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hn
    change Ideal.Quotient.mk I (a ^ n) * Ideal.Quotient.mk I a = 0 at hn
    rw [map_pow, ← pow_succ] at hn
    exact hu0 (IsReduced.eq_zero _ ⟨n + 1, hn⟩)
  have huunit : IsUnit (Ideal.Quotient.mk I a) := haunit.map (Ideal.Quotient.mk I)
  apply le_antisymm
  · intro t ht
    rw [hu]
    apply Ideal.le_radical
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Ideal.Quotient.mk I t * Ideal.Quotient.mk I a = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ht, zero_mul]
  · intro t ht
    rw [hu, Ideal.mem_radical_iff] at ht
    obtain ⟨n, hn⟩ := ht
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hn
    change Ideal.Quotient.mk I (t ^ n) * Ideal.Quotient.mk I a = 0 at hn
    have htpow : Ideal.Quotient.mk I (t ^ n) = 0 := huunit.mul_left_eq_zero.mp hn
    rw [map_pow] at htpow
    exact Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨n, htpow⟩)
