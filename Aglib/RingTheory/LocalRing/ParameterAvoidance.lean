/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Nakayama
/-!
# Parameters avoiding the minimal primes

Prime avoidance gives a first minimal generator outside every minimal prime
in a positive-dimensional noetherian local ring. A separate Nakayama argument
shows that a prime principal ideal with this avoidance property forces the
ring itself to be a domain. These statements do not assume regularity.

## Extraction basis

Transferred from `Quillen.Algebra.RegularLocal.ParameterAvoidance` at source revision
`83629578a3d70787d41ec631f5234af8758716af`, SHA-256
`293606b51e7c17c4eaea2520338f4737ac6fd7508afbc6d9079c8edeeeee7ba8`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
universe u
open IsLocalRing

namespace IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- In positive dimension, a first minimal generator can be chosen outside
all the minimal primes. The one nonprime ideal in prime avoidance is `m²`. -/
theorem exists_parameter_avoiding_minimalPrimes (hd : ringKrullDim R ≠ 0) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧
      ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  let m := maximalIdeal R
  have hsq : ¬m ≤ m ^ 2 := by
    intro h
    have hm : m = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m m
      m.fg_of_isNoetherianRing (by simpa only [smul_eq_mul, pow_two] using h)
      (by simp [m, IsLocalRing.jacobson_eq_maximalIdeal])
    exact hd (ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hm))
  have hmin : ∀ p ∈ minimalPrimes R, ¬m ≤ p := by
    intro p hp hle
    have he : m = p := (maximalIdeal.isMaximal R).eq_of_le hp.isPrime.ne_top hle
    have hmmin : m ∈ minimalPrimes R := he ▸ hp
    have hzero := Ideal.height_eq_zero_iff.mpr hmmin
    apply hd
    rw [← maximalIdeal_height_eq_ringKrullDim, hzero, WithBot.coe_zero]
  let S : Set (Ideal R) := insert (m ^ 2) (minimalPrimes R)
  have hfinite : S.Finite := (minimalPrimes.finite_of_isNoetherianRing R).insert _
  have hnot : ¬(m : Set R) ⊆ ⋃ p ∈ S, (p : Set R) := by
    rw [Ideal.subset_union_prime_finite hfinite (m ^ 2) (m ^ 2)
      (fun p hp hne _ => (Set.mem_insert_iff.mp hp).resolve_left hne |>.isPrime)]
    rintro ⟨p, hp, hle⟩
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact hsq hle
    · exact hmin p hp hle
  obtain ⟨x, hx, hxS⟩ := Set.not_subset.mp hnot
  refine ⟨x, hx, ?_, ?_⟩
  · intro hxsq
    exact hxS (Set.mem_iUnion.mpr ⟨m ^ 2, Set.mem_iUnion.mpr ⟨Set.mem_insert _ _, hxsq⟩⟩)
  · intro p hp hxp
    exact hxS (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨Set.mem_insert_of_mem _ hp, hxp⟩⟩)

/-- If `(x)` is prime and `x` is in the maximal ideal but outside the minimal
primes, then the noetherian local ring is a domain. A minimal prime below
`(x)` satisfies `q = xq`, so Nakayama makes it the zero ideal. -/
theorem isDomain_of_prime_parameter (x : R) (hx : x ∈ maximalIdeal R)
    (havoid : ∀ p ∈ minimalPrimes R, x ∉ p)
    (hprime : (Ideal.span {x}).IsPrime) : IsDomain R := by
  have := hprime
  obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le
    (show (⊥ : Ideal R) ≤ Ideal.span {x} from bot_le)
  have hxp : x ∉ p := havoid p hp
  have hpbot : p = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) p
      p.fg_of_isNoetherianRing
    · intro a ha
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hpx ha)
      have hbmem : b ∈ p := (hp.isPrime.mem_or_mem (hb ▸ ha)).resolve_left hxp
      rw [hb]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hbmem
    · rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hbot : (⊥ : Ideal R).IsPrime := hpbot ▸ hp.isPrime
  have : NoZeroDivisors R := ⟨by
    intro a b hab
    exact hbot.mem_or_mem (show a * b ∈ (⊥ : Ideal R) from hab)⟩
  exact NoZeroDivisors.to_isDomain R

end IsLocalRing
