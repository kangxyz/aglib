/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Tactic.Ring

/-!
# Sequential convergence and completeness for the actual valuation.
-/

@[expose] public noncomputable section

namespace Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- Sequential convergence expressed using the actual valuation. -/
def SeqTendsto (v : Valuation K Γ₀) (s : ℕ → K) (x : K) : Prop :=
  ∀ γ : Γ₀, γ ≠ 0 → ∃ N, ∀ n ≥ N, v (s n - x) < γ

/-- Sequential Cauchy condition expressed using the actual valuation. -/
def SeqCauchy (v : Valuation K Γ₀) (s : ℕ → K) : Prop :=
  ∀ γ : Γ₀, γ ≠ 0 → ∃ N, ∀ m ≥ N, ∀ n ≥ N, v (s m - s n) < γ

/-- Genuine convergence of every valuation-Cauchy sequence. -/
def IsSeqComplete (v : Valuation K Γ₀) : Prop :=
  ∀ s : ℕ → K, v.SeqCauchy s → ∃ x, v.SeqTendsto s x

/-- A subset is sequentially complete with respect to the ambient valuation. -/
def IsSeqCompleteSet (v : Valuation K Γ₀) (S : Set K) : Prop :=
  ∀ s : ℕ → K, (∀ n, s n ∈ S) → v.SeqCauchy s →
    ∃ x ∈ S, v.SeqTendsto s x

variable (v : Valuation K Γ₀)

theorem SeqTendsto.cauchy {s : ℕ → K} {x : K} (h : v.SeqTendsto s x) :
    v.SeqCauchy s := by
  intro γ hγ
  obtain ⟨N, hN⟩ := h γ hγ
  refine ⟨N, fun m hm n hn => ?_⟩
  simpa only [sub_sub_sub_cancel_right] using v.map_sub_lt (hN m hm) (hN n hn)

theorem SeqTendsto.unique {s : ℕ → K} {x y : K}
    (hx : v.SeqTendsto s x) (hy : v.SeqTendsto s y) : x = y := by
  by_contra hxy
  have hv : v (x - y) ≠ 0 := by simpa using sub_ne_zero.mpr hxy
  obtain ⟨N, hN⟩ := hx (v (x - y)) hv
  obtain ⟨M, hM⟩ := hy (v (x - y)) hv
  have h := v.map_sub_lt (hM (max N M) (le_max_right _ _))
    (hN (max N M) (le_max_left _ _))
  have heq : (s (max N M) - y) - (s (max N M) - x) = x - y := by ring
  rw [heq] at h
  exact lt_irrefl _ h

theorem SeqTendsto.mul_const {s : ℕ → K} {x : K}
    (h : v.SeqTendsto s x) (a : K) : v.SeqTendsto (fun n => s n * a) (x * a) := by
  by_cases ha : a = 0
  · subst a
    intro γ hγ
    exact ⟨0, fun n hn => by simpa using (pos_iff_ne_zero.mpr hγ)⟩
  intro γ hγ
  have hva : v a ≠ 0 := by simpa using ha
  obtain ⟨N, hN⟩ := h (γ / v a) (div_ne_zero hγ hva)
  refine ⟨N, fun n hn => ?_⟩
  rw [← sub_mul, map_mul]
  exact (lt_div_iff₀ (pos_iff_ne_zero.mpr hva)).mp (hN n hn)

theorem SeqTendsto.add {s t : ℕ → K} {x y : K}
    (hs : v.SeqTendsto s x) (ht : v.SeqTendsto t y) :
    v.SeqTendsto (fun n => s n + t n) (x + y) := by
  intro γ hγ
  obtain ⟨N, hN⟩ := hs γ hγ
  obtain ⟨M, hM⟩ := ht γ hγ
  refine ⟨max N M, fun n hn => ?_⟩
  have heq : s n + t n - (x + y) = (s n - x) + (t n - y) := by ring
  rw [heq]
  exact (v.map_add _ _).trans_lt (max_lt
    (hN n ((le_max_left _ _).trans hn)) (hM n ((le_max_right _ _).trans hn)))

/-- Taking a positive power does not enlarge an element of the unit interval. -/
private theorem pow_le_self_of_le_one {a : Γ₀} (ha : a ≤ 1)
    {p : ℕ} (hp : 0 < p) : a ^ p ≤ a := by
  simpa only [pow_one] using
    pow_le_pow_right_of_le_one' ha (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp))

variable (p : ℕ) [ExpChar K p]

/-- Roots of a Frobenius-Cauchy sequence are Cauchy; no inverse Frobenius on `K` is used. -/
theorem seqCauchy_of_pow (s : ℕ → K)
    (h : v.SeqCauchy (fun n => s n ^ p)) : v.SeqCauchy s := by
  intro γ hγ
  obtain ⟨N, hN⟩ := h (γ ^ p) (pow_ne_zero _ hγ)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hh : v (s m - s n) ^ p < γ ^ p := by
    simpa only [← map_pow, sub_pow_expChar] using hN m hm n hn
  exact lt_of_pow_lt_pow_left₀ p (zero_le : 0 ≤ γ) hh

/-- Frobenius is sequentially continuous for the valuation topology. -/
theorem SeqTendsto.pow {s : ℕ → K} {x : K} (h : v.SeqTendsto s x)
    (hp : 0 < p) : v.SeqTendsto (fun n => s n ^ p) (x ^ p) := by
  intro γ hγ
  have hm : min γ 1 ≠ 0 := ne_of_gt (lt_min (pos_iff_ne_zero.mpr hγ) zero_lt_one)
  obtain ⟨N, hN⟩ := h (min γ 1) hm
  refine ⟨N, fun n hn => ?_⟩
  rw [← sub_pow_expChar, map_pow]
  have hh := hN n hn
  exact (pow_le_self_of_le_one (hh.le.trans (min_le_right _ _)) hp).trans_lt
    (hh.trans_le (min_le_left _ _))

/-- The literal Frobenius subfield is complete in the induced valuation.
The witness is the limit of an actual sequence of chosen roots in `K`. -/
theorem isSeqCompleteSet_frobeniusFieldRange (hK : v.IsSeqComplete)
    (hp : 0 < p) :
    v.IsSeqCompleteSet ((frobenius K p).fieldRange : Set K) := by
  intro s hs hc
  have hroot : ∀ n, ∃ x : K, x ^ p = s n := by
    intro n
    have hn := hs n
    change ∃ x : K, frobenius K p x = s n at hn
    simpa only [frobenius_def] using hn
  choose t ht using hroot
  have hct : v.SeqCauchy t := Valuation.seqCauchy_of_pow v p t (by simpa only [ht] using hc)
  obtain ⟨x, hx⟩ := hK t hct
  refine ⟨x ^ p, ?_, ?_⟩
  · exact ⟨x, rfl⟩
  · simpa only [ht] using Valuation.SeqTendsto.pow v p hx hp

end Valuation
