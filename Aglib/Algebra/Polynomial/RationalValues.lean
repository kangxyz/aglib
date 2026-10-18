/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Instances.Rat

/-!
# Values of rational polynomials at integers

Three facts about rational polynomials used by the re-indexing of the flattening stratification
by Hilbert polynomials (Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, proof of Thm 4.3, pp. 22–23):

* `Polynomial.eq_of_natDegree_le_of_eval_add_eq`: two polynomials of degree at most `n` that
  agree at the `n + 1` consecutive integers `N, …, N + n` are equal;
* `Polynomial.eventually_nonneg_or_eventually_neg`: a polynomial is eventually nonnegative or
  eventually negative on the natural numbers;
* `Polynomial.exists_eval_le_imp_eventually_le`: for finitely many polynomials and any `N`, one
  value `p ≥ N` orders them eventually: `f(p) ≤ g(p)` implies `f(m) ≤ g(m)` for all `m ≫ 0`.
-/

@[expose] public section

open scoped Polynomial

namespace Polynomial

/-- **Re-indexing by polynomials** (Nitsure, arXiv:math/0504590v1, proof of Thm 4.3, p. 22): two
rational polynomials of degree at most `n` that agree at the `n + 1` integers `N, …, N + n` are
equal; so `f ↦ (f(N), …, f(N + n))` is injective on polynomials of degree `≤ n`. -/
theorem eq_of_natDegree_le_of_eval_add_eq {f g : ℚ[X]} {n : ℕ} (hf : f.natDegree ≤ n)
    (hg : g.natDegree ≤ n) (N : ℤ)
    (h : ∀ j : ℕ, j ≤ n → f.eval ((N + j : ℤ) : ℚ) = g.eval ((N + j : ℤ) : ℚ)) : f = g := by
  classical
  let s : Finset ℚ := (Finset.range (n + 1)).image fun j : ℕ => ((N + j : ℤ) : ℚ)
  have hs : s.card = n + 1 := by
    rw [Finset.card_image_of_injective _ fun a b hab => by simpa using hab, Finset.card_range]
  have hdeg : ∀ p : ℚ[X], p.natDegree ≤ n → p.degree < s.card := fun p hp => by
    rw [hs]
    exact (Polynomial.degree_le_of_natDegree_le hp).trans_lt
      (by exact_mod_cast Nat.lt_succ_self n)
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq s (hdeg f hf) (hdeg g hg) ?_
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  exact h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

/-- A rational polynomial is eventually nonnegative or eventually negative on the natural
numbers. -/
theorem eventually_nonneg_or_eventually_neg (h : ℚ[X]) :
    (∀ᶠ m : ℕ in Filter.atTop, 0 ≤ h.eval (m : ℚ)) ∨
      ∀ᶠ m : ℕ in Filter.atTop, h.eval (m : ℚ) < 0 := by
  by_cases hdeg : 0 < h.degree
  · rcases le_or_gt 0 h.leadingCoeff with hc | hc
    · exact Or.inl (((Polynomial.tendsto_atTop_of_leadingCoeff_nonneg h hdeg hc).comp
        tendsto_natCast_atTop_atTop).eventually_ge_atTop 0)
    · exact Or.inr (((Polynomial.tendsto_atBot_of_leadingCoeff_nonpos h hdeg hc.le).comp
        tendsto_natCast_atTop_atTop).eventually_lt_atBot 0)
  · rw [Polynomial.eq_C_of_degree_le_zero (not_lt.mp hdeg)]
    simp only [Polynomial.eval_C]
    rcases le_or_gt 0 (h.coeff 0) with hc | hc
    · exact Or.inl (Filter.Eventually.of_forall fun _ => hc)
    · exact Or.inr (Filter.Eventually.of_forall fun _ => hc)

/-- **One value orders finitely many polynomials** (Nitsure, arXiv:math/0504590v1, proof of
Thm 4.3 (iii), p. 23): for a finite set `I` of rational polynomials and any `N`, there is
`p ≥ N` such that for `f, g ∈ I`, `f(p) ≤ g(p)` implies `f(m) ≤ g(m)` for all `m ≫ 0`. -/
theorem exists_eval_le_imp_eventually_le {I : Set ℚ[X]} (hI : I.Finite) (N : ℕ) :
    ∃ p : ℕ, N ≤ p ∧ ∀ f ∈ I, ∀ g ∈ I, f.eval (p : ℚ) ≤ g.eval (p : ℚ) →
      ∀ᶠ m : ℕ in Filter.atTop, f.eval (m : ℚ) ≤ g.eval (m : ℚ) := by
  classical
  have hpair : ∀ f ∈ I, ∀ g ∈ I, ∀ᶠ m : ℕ in Filter.atTop,
      (¬∀ᶠ k : ℕ in Filter.atTop, f.eval (k : ℚ) ≤ g.eval (k : ℚ)) →
        g.eval (m : ℚ) < f.eval (m : ℚ) :=
    fun f _ g _ => by
      rcases eventually_nonneg_or_eventually_neg (g - f) with h | h
      · refine Filter.Eventually.of_forall fun m hfg => absurd ?_ hfg
        filter_upwards [h] with k hk
        simpa [Polynomial.eval_sub, sub_nonneg] using hk
      · filter_upwards [h] with m hm _
        simpa [Polynomial.eval_sub, sub_neg] using hm
  have hall : ∀ᶠ m : ℕ in Filter.atTop, N ≤ m ∧ ∀ f ∈ I, ∀ g ∈ I,
      (¬∀ᶠ k : ℕ in Filter.atTop, f.eval (k : ℚ) ≤ g.eval (k : ℚ)) →
        g.eval (m : ℚ) < f.eval (m : ℚ) :=
    (Filter.eventually_ge_atTop N).and ((Filter.eventually_all_finite hI).mpr fun f hf =>
      (Filter.eventually_all_finite hI).mpr fun g hg => hpair f hf g hg)
  obtain ⟨p, hNp, hp⟩ := hall.exists
  exact ⟨p, hNp, fun f hf g hg hfg => by_contra fun h => (hp f hf g hg h).not_ge hfg⟩

end Polynomial
