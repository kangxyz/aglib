/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
A local dimension bound from height bounds on a principal open.
The proof uses finite prime avoidance and the height theorem only.

## Extraction basis

Transferred from `R5Lab.RingTheory.KrullDimension.PrincipalOpenBound` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`6b3eef3e665da1ba177e95a6181757193ccef302286c2ce298add2e9b4b6038e`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
universe u
open IsLocalRing

namespace Ideal

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Minimal primes of a nonzero principal ideal in a domain have height one. -/
theorem height_eq_one_of_mem_minimalPrimes_span [IsDomain R]
    {t : R} (ht : t ≠ 0) {P : Ideal R} (hP : P ∈ (Ideal.span {t}).minimalPrimes) :
    P.height = 1 := by
  have := hP.isPrime
  apply le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP)
  apply Order.one_le_iff_ne_zero.mpr
  intro hzero
  have hbot : P = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hzero
  have htP : t ∈ P := hP.le (Ideal.mem_span_singleton_self t)
  exact ht (show t ∈ (⊥ : Ideal R) from hbot ▸ htP)

/-- A two-generator ideal has minimal primes of height at most two. -/
theorem height_le_two_of_mem_minimalPrimes_span_pair
    {a b : R} {P : Ideal R} (hP : P ∈ (Ideal.span {a, b}).minimalPrimes) :
    P.height ≤ 2 := by
  classical
  have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (p := P) (s := {a, b}) (by simpa using hP)
  exact h.trans (by exact_mod_cast (Finset.card_insert_le a {b}).trans (by simp))

omit [IsNoetherianRing R] in
/-- A finite collection of primes of bounded height can be avoided inside a
strictly higher-dimensional maximal ideal. -/
theorem _root_.IsLocalRing.exists_mem_maximalIdeal_avoiding [IsLocalRing R]
    (S : Set (Ideal R)) (hS : S.Finite) (n : ℕ)
    (hprime : ∀ P ∈ S, P.IsPrime) (hheight : ∀ P ∈ S, P.height ≤ n)
    (hn : (n : ℕ∞) < (maximalIdeal R).height) :
    ∃ a : R, a ∈ maximalIdeal R ∧ ∀ P ∈ S, a ∉ P := by
  have hnot : ¬(maximalIdeal R : Set R) ⊆ ⋃ P ∈ S, (P : Set R) := by
    rw [Ideal.subset_union_prime_finite hS (⊥ : Ideal R) (⊥ : Ideal R)
      (fun P hP _ _ => hprime P hP)]
    rintro ⟨P, hP, hle⟩
    have he := (maximalIdeal.isMaximal R).eq_of_le (hprime P hP).ne_top hle
    exact (not_le_of_gt hn) (he ▸ hheight P hP)
  obtain ⟨a, ham, ha⟩ := Set.not_subset.mp hnot
  refine ⟨a, ham, fun P hP haP => ?_⟩
  exact ha (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP, haP⟩⟩)

/-- Adjoining an element outside all minimal primes of a nonzero principal
ideal forces height at least two at every containing prime. -/
theorem two_le_height_of_mem_pair [IsDomain R]
    {t a : R} (ht : t ≠ 0)
    (ha : ∀ P ∈ (Ideal.span {t}).minimalPrimes, a ∉ P)
    (Q : Ideal R) [Q.IsPrime] (htQ : t ∈ Q) (haQ : a ∈ Q) :
    2 ≤ Q.height := by
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem Q).mpr htQ)
  have := hP.isPrime
  have hlt : P < Q := lt_of_le_of_ne hPQ (fun he => ha P hP (he.symm ▸ haQ))
  have hh := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  norm_num [height_eq_one_of_mem_minimalPrimes_span ht hP] at hh ⊢
  exact hh

/-- A Noetherian local domain with all primes on a nonempty principal open of
height at most one has local dimension at most two. -/
theorem _root_.IsLocalRing.ringKrullDim_le_two_of_principal_open_height_le_one
    [IsLocalRing R] [IsDomain R] (t : R) (ht : t ≠ 0)
    (hopen : ∀ P : Ideal R, P.IsPrime → t ∉ P → P.height ≤ 1) :
    ringKrullDim R ≤ 2 := by
  by_contra hdim
  have hm : (2 : ℕ∞) < (maximalIdeal R).height := by
    have h := lt_of_not_ge hdim
    rw [← maximalIdeal_height_eq_ringKrullDim] at h
    exact WithBot.coe_lt_coe.mp h
  have htm : t ∈ maximalIdeal R := by
    by_contra ht'
    exact (not_le_of_gt hm) ((hopen _ (maximalIdeal.isMaximal R).isPrime ht').trans (by norm_num))
  obtain ⟨a, ham, ha⟩ := IsLocalRing.exists_mem_maximalIdeal_avoiding
    (Ideal.span {t}).minimalPrimes (Ideal.finite_minimalPrimes_of_isNoetherianRing R _)
    1 (fun _ hP => hP.isPrime)
    (fun P hP => Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)
    (lt_trans (by norm_num) hm)
  have htproper : Ideal.span {t} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr htm)
  have ha0 : a ≠ 0 := by
    obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes htproper
    intro e
    exact ha P hP (e ▸ P.zero_mem)
  let J : Ideal R := Ideal.span {t, a}
  let I : Ideal R := Ideal.span {a}
  let S : Set (Ideal R) := J.minimalPrimes ∪ I.minimalPrimes
  have hS : S.Finite := (Ideal.finite_minimalPrimes_of_isNoetherianRing R J).union
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R I)
  obtain ⟨b, hbm, hb⟩ := IsLocalRing.exists_mem_maximalIdeal_avoiding S hS 2
    (fun P hP => hP.elim (fun h => h.isPrime) (fun h => h.isPrime))
    (fun P hP => hP.elim (fun h => height_le_two_of_mem_minimalPrimes_span_pair h)
      (fun h =>
        (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I P h).trans (by norm_num))) hm
  have hproper : Ideal.span ({a, b} : Set R) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
    exact Ideal.span_le.mpr (by
      simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe] using
        And.intro ham hbm)
  obtain ⟨Q, hQ⟩ := Ideal.nonempty_minimalPrimes hproper
  have := hQ.isPrime
  have haQ : a ∈ Q := hQ.le (Ideal.subset_span (by simp))
  have hbQ : b ∈ Q := hQ.le (Ideal.subset_span (by simp))
  have hQle : Q.height ≤ 2 := height_le_two_of_mem_minimalPrimes_span_pair hQ
  have hQge : 2 ≤ Q.height := two_le_height_of_mem_pair ha0
    (fun P hP => hb P (Or.inr hP)) Q haQ hbQ
  have htQ : t ∉ Q := by
    intro htQ
    have hJQ : J ≤ Q := Ideal.span_le.mpr (by
      simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe] using
        And.intro htQ haQ)
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hJQ
    have := hP.isPrime
    have htP : t ∈ P := hP.le (Ideal.subset_span (by simp))
    have haP : a ∈ P := hP.le (Ideal.subset_span (by simp))
    have hPge : 2 ≤ P.height := two_le_height_of_mem_pair ht ha P htP haP
    have he : P = Q := P.eq_of_le_of_height_le hPQ (hQle.trans hPge)
    exact hb P (Or.inl hP) (he.symm ▸ hbQ)
  have hh : (2 : ℕ∞) ≤ 1 := hQge.trans (hopen Q inferInstance htQ)
  norm_num at hh

end Ideal
