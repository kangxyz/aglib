/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.Module

/-!
# Surjectivity of a Frobenius-semilinear difference

On a finite-dimensional vector space over a separably closed field of positive
characteristic, a Frobenius-semilinear endomorphism minus the identity is
surjective as an additive map. The field need not be perfect, and the
endomorphism need not be invertible.
-/

@[expose] public section

open Function Polynomial

namespace LinearMap

private theorem exists_eq_sum_range_smul
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (u : ℕ → V) :
    ∃ n : ℕ, ∃ a : ℕ → k, u n = ∑ i ∈ Finset.range n, a i • u i := by
  classical
  obtain ⟨b, hb, hb0⟩ := not_linearIndependent_iff_finsupp.mp
    (Module.Finite.not_linearIndependent_of_infinite (R := k) u)
  have hs : b.support.Nonempty := Finsupp.support_nonempty_iff.mpr hb0
  let n := b.support.max' hs
  have hn : n ∈ b.support := Finset.max'_mem _ hs
  have hbn : b n ≠ 0 := Finsupp.mem_support_iff.mp hn
  have hsupport : b.support ⊆ Finset.range (n + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.le_max' _ i hi))
  have hsum : ∑ i ∈ Finset.range (n + 1), b i • u i = 0 := by
    calc
      ∑ i ∈ Finset.range (n + 1), b i • u i =
          ∑ i ∈ b.support, b i • u i := by
        symm
        apply Finset.sum_subset hsupport
        intro i _ hi
        simp [Finsupp.notMem_support_iff.mp hi]
      _ = 0 := hb
  rw [Finset.sum_range_succ] at hsum
  have hlast : b n • u n = -(∑ i ∈ Finset.range n, b i • u i) :=
    eq_neg_of_add_eq_zero_right hsum
  refine ⟨n, fun i => -(b n)⁻¹ * b i, ?_⟩
  calc
    u n = (b n)⁻¹ • (b n • u n) := by simp [smul_smul, hbn]
    _ = (b n)⁻¹ • (-(∑ i ∈ Finset.range n, b i • u i)) := by rw [hlast]
    _ = ∑ i ∈ Finset.range n, (-(b n)⁻¹ * b i) • u i := by
      simp [Finset.smul_sum, smul_smul, Finset.sum_neg_distrib]

private noncomputable def differencePolynomial {k : Type*} [Field k] (p : ℕ) (a : ℕ → k) :
    ℕ → k[X]
  | 0 => -1
  | n + 1 => differencePolynomial p a n ^ p + C (a n) * X ^ p

private theorem derivative_differencePolynomial
    {k : Type*} [Field k] (p : ℕ) [CharP k p] (a : ℕ → k) (n : ℕ) :
    (differencePolynomial p a n).derivative = 0 := by
  cases n <;> simp [differencePolynomial, derivative_pow]

private theorem exists_differencePolynomial_eval_eq
    {k : Type*} [Field k] [IsSepClosed k] (p : ℕ) [CharP k p]
    (a : ℕ → k) (n : ℕ) :
    ∃ t : k, (differencePolynomial p a n).eval t = t := by
  let P := differencePolynomial p a n - X
  have hderiv : P.derivative = -1 := by
    simp [P, derivative_differencePolynomial]
  have hdegree : P.degree ≠ 0 := degree_ne_of_natDegree_ne (by
    intro h
    have hzero := derivative_of_natDegree_zero h
    rw [hderiv] at hzero
    exact neg_ne_zero.mpr one_ne_zero hzero)
  have hsep : P.Separable := by
    rw [separable_def, hderiv]
    exact ⟨0, -1, by simp⟩
  obtain ⟨t, ht⟩ := IsSepClosed.exists_root P hdegree hsep
  refine ⟨t, sub_eq_zero.mp ?_⟩
  simpa [Polynomial.IsRoot, P] using ht

private theorem difference_sum_identity
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (F : V →ₛₗ[_root_.frobenius k p] V) (v : V) (a : ℕ → k) (t : k) (n : ℕ) :
    F (∑ i ∈ Finset.range n,
        (differencePolynomial p a (i + 1)).eval t • ((F : V → V)^[i]) v) -
        (∑ i ∈ Finset.range n,
          (differencePolynomial p a (i + 1)).eval t • ((F : V → V)^[i]) v) =
      ((differencePolynomial p a n).eval t) ^ p • ((F : V → V)^[n]) v -
        t ^ p • (∑ i ∈ Finset.range n, a i • ((F : V → V)^[i]) v) + v := by
  induction n with
  | zero =>
    have hneg : (-1 : k) ^ p = -1 := by
      change _root_.frobenius k p (-1) = -1
      simp
    simp [differencePolynomial, hneg]
  | succ n ih =>
    have hF := (sub_eq_iff_eq_add).mp ih
    simp only [Finset.sum_range_succ, map_add, map_smulₛₗ, _root_.frobenius_def]
    rw [hF]
    simp only [differencePolynomial, eval_add, eval_pow, eval_mul, eval_C, eval_X,
      Function.iterate_succ_apply']
    module

/-- On a finite-dimensional vector space over a separably closed field of
characteristic `p`, a Frobenius-semilinear map minus the identity is surjective.
No perfectness or invertibility hypothesis is required. -/
theorem surjective_sub_id_of_frobenius
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsSepClosed k]
    [FiniteDimensional k V]
    (F : V →ₛₗ[_root_.frobenius k p] V) :
    Function.Surjective (fun v : V => F v - v) := by
  intro v
  obtain ⟨n, a, hrelation⟩ := exists_eq_sum_range_smul
    (k := k) (fun i => ((F : V → V)^[i]) v)
  obtain ⟨t, ht⟩ := exists_differencePolynomial_eval_eq p a n
  refine ⟨∑ i ∈ Finset.range n,
    (differencePolynomial p a (i + 1)).eval t • ((F : V → V)^[i]) v, ?_⟩
  dsimp only
  rw [difference_sum_identity, ht, hrelation]
  simp

end LinearMap
