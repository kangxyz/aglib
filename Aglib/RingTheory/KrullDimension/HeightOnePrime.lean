/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
A height-one prime avoiding a prescribed nonzero nonunit in a Noetherian local
 domain of dimension greater than one. This is the local prime-avoidance step
for LG-09; it does not assume regularity, normality, or unique factorization.

## Extraction basis

Transferred from `R5Lab.RingTheory.KrullDimension.HorizontalPrime` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`93fe04e9bdd86badc55114f3a11faa205175813732c1eeb0aab5d5a5d223437b`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

/-- A local domain of dimension at least two has a height-one prime avoiding
any prescribed nonzero nonunit. -/
theorem exists_heightOne_prime_not_mem
    (hdim : 1 < ringKrullDim R) (π : R) (hπ : π ≠ 0) (hπunit : ¬ IsUnit π) :
    ∃ q : Ideal R, q.IsPrime ∧ q.height = 1 ∧ π ∉ q := by
  classical
  let I : Ideal R := Ideal.span {π}
  have hI : I ≠ ⊤ := by simpa [I] using hπunit
  have havoid : ¬ ((maximalIdeal R : Set R) ⊆
      ⋃ p ∈ I.minimalPrimes, (p : Set R)) := by
    intro hcover
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime_finite
      (Ideal.finite_minimalPrimes_of_isNoetherianRing R I)
      (f := id) (⊥ : Ideal R) ⊥ (fun p hp _ _ => hp.isPrime)).mp hcover
    have hpheight := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I p hp
    have hmheight : (maximalIdeal R).height ≤ 1 :=
      (Ideal.height_mono hmp).trans hpheight
    have hbound : ringKrullDim R ≤ 1 := by
      rw [← maximalIdeal_height_eq_ringKrullDim]
      exact_mod_cast hmheight
    exact (not_le_of_gt hdim) hbound
  obtain ⟨a, ham, haavoid⟩ := Set.not_subset.mp havoid
  have ha : ∀ p ∈ I.minimalPrimes, a ∉ p := by
    intro p hp hap
    apply haavoid
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hap⟩⟩
  have ha0 : a ≠ 0 := by
    obtain ⟨p, hp⟩ := I.nonempty_minimalPrimes hI
    intro h
    exact ha p hp (h ▸ p.zero_mem)
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le
    ((maximalIdeal R).span_singleton_le_iff_mem.mpr ham)
  have hqprime : q.IsPrime := hq.isPrime
  let : q.IsPrime := hqprime
  have haq : a ∈ q := hq.le (Ideal.subset_span (Set.mem_singleton a))
  have hq0 : q ≠ ⊥ := by
    intro hqbot
    exact ha0 (by simpa [hqbot] using haq)
  have hqheight : q.height = 1 := by
    apply le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {a}) q hq)
    exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hq0)
  refine ⟨q, hqprime, hqheight, ?_⟩
  intro hπq
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le
    (show I ≤ q from q.span_singleton_le_iff_mem.mpr hπq)
  let : p.IsPrime := hp.isPrime
  have hp0 : p ≠ ⊥ := by
    intro hpbot
    have hπp : π ∈ p := hp.le (Ideal.subset_span (Set.mem_singleton π))
    exact hπ (by simpa [hpbot] using hπp)
  have hple : 1 ≤ p.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hp0)
  have hp_eq_q : p = q := p.eq_of_le_of_height_le hpq (hqheight ▸ hple)
  exact ha p hp (hp_eq_q.symm ▸ haq)

end IsLocalRing
