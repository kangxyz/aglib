/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Common nonzero zeros over an algebraically closed field

The origin has height at least the number of variables, by the explicit chain
which successively kills the variables. Nullstellensatz and Krull's height theorem
then give a nonzero common zero for fewer equations vanishing at the origin.
-/

@[expose] public section

namespace MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

private noncomputable def killInitial (i : ℕ) :
    MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K :=
  eval₂Hom C (fun j => if j.val < i then 0 else X j)

private lemma killInitial_comp {i j : ℕ} (h : i ≤ j) :
    (killInitial (K := K) (n := n) j).comp (killInitial i) = killInitial j := by
  apply ringHom_ext
  · intro a
    simp [killInitial]
  · intro a
    by_cases hi : a.val < i
    · have hj : a.val < j := hi.trans_le h
      simp [killInitial, hi, hj]
    · simp [killInitial, hi]

private lemma killInitial_ker_lt {i : ℕ} (hi : i < n) :
    RingHom.ker (killInitial (K := K) (n := n) i) <
      RingHom.ker (killInitial (i + 1)) := by
  refine lt_of_le_of_ne ?_ ?_
  · intro p hp
    change killInitial (i + 1) p = 0
    rw [← killInitial_comp (Nat.le_succ i), RingHom.comp_apply]
    rw [show killInitial i p = 0 from hp, map_zero]
  · intro heq
    have hx : X (⟨i, hi⟩ : Fin n) ∈ RingHom.ker (killInitial (K := K) (i + 1)) := by
      simp [RingHom.mem_ker, killInitial]
    rw [← heq] at hx
    simp [RingHom.mem_ker, killInitial] at hx

private lemma le_height_killInitial {i : ℕ} (hi : i ≤ n) :
    (i : ℕ∞) ≤ (RingHom.ker (killInitial (K := K) (n := n) i)).height := by
  induction i with
  | zero => exact bot_le
  | succ i ih =>
    let := RingHom.ker_isPrime (killInitial (K := K) (n := n) i)
    let := RingHom.ker_isPrime (killInitial (K := K) (n := n) (i + 1))
    have h := Ideal.height_add_one_le_of_lt_of_isPrime
      (killInitial_ker_lt (K := K) (Nat.lt_of_succ_le hi))
    calc
      ((i + 1 : ℕ) : ℕ∞) = (i : ℕ∞) + 1 := by simp
      _ ≤ (RingHom.ker (killInitial (K := K) (n := n) i)).height + 1 :=
        add_le_add (ih (Nat.le_of_succ_le hi)) le_rfl
      _ ≤ _ := h

/-- The ideal of the origin in affine `n`-space has height at least `n`. -/
theorem le_height_vanishingIdeal_origin :
    (n : ℕ∞) ≤ (vanishingIdeal K ({0} : Set (Fin n → K))).height := by
  have heq : RingHom.ker (killInitial (K := K) (n := n) n) =
      vanishingIdeal K ({0} : Set (Fin n → K)) := by
    ext p
    rw [RingHom.mem_ker, mem_vanishingIdeal_singleton_iff]
    have hmap : killInitial (K := K) (n := n) n = C.comp (eval 0) := by
      ext a <;> simp [killInitial]
    rw [hmap, RingHom.comp_apply]
    simp
  rw [← heq]
  exact le_height_killInitial le_rfl

/-- Fewer than `n` equations vanishing at the origin in affine `n`-space over an
algebraically closed field have a common nonzero zero. No homogeneity is needed. -/
theorem exists_ne_zero_common_zero [IsAlgClosed K] (s : Finset (MvPolynomial (Fin n) K))
    (hzero : ∀ p ∈ s, eval 0 p = 0) (hcard : s.card < n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∀ p ∈ s, eval x p = 0 := by
  classical
  by_contra! h
  let I : Ideal (MvPolynomial (Fin n) K) := Ideal.span (s : Set _)
  have hZ : zeroLocus K I = {0} := by
    rw [show I = Ideal.span (s : Set _) from rfl, zeroLocus_span]
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hx0
      obtain ⟨p, hp, hpx⟩ := h x hx0
      exact hpx (hx p hp)
    · rintro rfl
      exact hzero
  have hrad : I.radical = vanishingIdeal K ({0} : Set (Fin n → K)) := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), hZ]
  have hmin : vanishingIdeal K ({0} : Set (Fin n → K)) ∈ I.minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hheight := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have hn := (le_height_vanishingIdeal_origin (K := K) (n := n)).trans hheight
  exact (not_le_of_gt hcard) (by exact_mod_cast hn)

end MvPolynomial
