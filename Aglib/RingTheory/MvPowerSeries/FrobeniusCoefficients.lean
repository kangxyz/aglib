/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Frobenius coefficient independence for multivariate power series

Finite independence over the Frobenius subfield and separation of exponent
residue classes give independence against power-series p-th powers.
-/

@[expose] public noncomputable section

namespace MvPowerSeries


variable {k σ ι : Type*} [Field k] (p : ℕ) (hp : p ≠ 0) [ExpChar k p]

include hp

/-- A coefficient of a p-th power at a p-divisible exponent. -/
lemma coeff_pow_smul (f : MvPowerSeries σ k) (m : σ →₀ ℕ) :
    coeff (p • m) (f ^ p) = (coeff m f) ^ p := by
  rw [← map_frobenius_expand p hp, coeff_map, coeff_expand_smul]
  rfl

/-- A p-th power has no coefficient outside p-divisible exponent vectors. -/
lemma coeff_pow_of_not_dvd (f : MvPowerSeries σ k) (m : σ →₀ ℕ)
    (i : σ) (hi : ¬ p ∣ m i) : coeff m (f ^ p) = 0 := by
  rw [← map_frobenius_expand p hp, coeff_map, coeff_expand_of_not_dvd p hp f hi,
    map_zero]

/-- Finite independence over the literal Frobenius subfield survives series p-th-power
coefficients. No roots are assumed to exist in k outside that subfield. -/
lemma sum_smul_pow_eq_zero
    [Fintype ι] {b : ι → k}
    (hb : LinearIndependent (frobenius k p).fieldRange b)
    (f : ι → MvPowerSeries σ k)
    (h : ∑ i, b i • (f i ^ p) = 0) : ∀ i, f i = 0 := by
  classical
  have hcoeff (m : σ →₀ ℕ) : ∑ i, b i * (coeff m (f i)) ^ p = 0 := by
    have hm := congrArg (coeff (p • m)) h
    simpa only [map_sum, coeff_smul, coeff_pow_smul p hp, coeff_zero] using hm
  have hc (m : σ →₀ ℕ) (i : ι) : coeff m (f i) = 0 := by
    let c : ι → (frobenius k p).fieldRange :=
      fun j => (frobenius k p).rangeRestrictField (coeff m (f j))
    have hs : ∑ j, c j • b j = 0 := by
      change ∑ j, (coeff m (f j)) ^ p * b j = 0
      simpa only [mul_comm] using hcoeff m
    have hc0 := Fintype.linearIndependent_iff.mp hb c hs i
    have hp0 : (coeff m (f i)) ^ p = 0 := congrArg Subtype.val hc0
    exact eq_zero_of_pow_eq_zero hp0
  intro i
  exact MvPowerSeries.ext fun m => by simpa only [coeff_zero] using hc m i

/-- Distinct residue classes cannot contribute to the same coefficient. -/
lemma coeff_monomial_mul_pow_other_residue
    (f : MvPowerSeries σ k) (a : k) (e r m : σ →₀ ℕ)
    (he : ∀ x, e x < p) (hr : ∀ x, r x < p) (hne : e ≠ r) :
    coeff (r + p • m) (monomial e a * f ^ p) = 0 := by
  classical
  rw [coeff_monomial_mul]
  split_ifs with hle
  · have hex : ∃ x, e x ≠ r x := by
      by_contra h
      push Not at h
      exact hne (Finsupp.ext h)
    obtain ⟨x, hx⟩ := hex
    have hnd : ¬ p ∣ (r + p • m - e) x := by
      intro hd
      obtain ⟨q, hq⟩ := hd
      have heq : r x + p * m x = e x + p * q := by
        have hs := Nat.sub_add_cancel (show e x ≤ (r + p • m) x from hle x)
        rw [← Finsupp.tsub_apply, hq] at hs
        simpa only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, add_comm] using hs.symm
      have hm := congrArg (fun n : ℕ => n % p) heq
      have hsame : r x = e x := by
        simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
          add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (hr x), Nat.mod_eq_of_lt (he x)] using hm
      exact hx hsame.symm
    rw [coeff_pow_of_not_dvd p hp f _ x hnd, mul_zero]
  · rfl

/-- Coefficient-level form of independence of b_j X^r over p-th powers of the
series ring. This is the non-perfect-field core; both index families are finite. -/
lemma sum_monomial_mul_pow_eq_zero
    {ρ : Type*} [Fintype ι] [Fintype ρ]
    {b : ι → k} (hb : LinearIndependent (frobenius k p).fieldRange b)
    (r : ρ → σ →₀ ℕ) (hr : ∀ j x, r j x < p) (hinj : Function.Injective r)
    (f : ρ → ι → MvPowerSeries σ k)
    (h : ∑ j, ∑ i, monomial (r j) (b i) * f j i ^ p = 0) :
    ∀ j i, f j i = 0 := by
  classical
  have hc (j : ρ) (m : σ →₀ ℕ) :
      ∑ i, b i * (coeff m (f j i)) ^ p = 0 := by
    have hm := congrArg (coeff (r j + p • m)) h
    simp only [map_sum, coeff_zero] at hm
    rw [Finset.sum_eq_single j] at hm
    · simpa only [coeff_add_monomial_mul, coeff_pow_smul p hp] using hm
    · intro j' hj' hne
      apply Finset.sum_eq_zero
      intro i hi
      exact coeff_monomial_mul_pow_other_residue p hp (f j' i) (b i)
        (r j') (r j) m (hr j') (hr j) (fun heq => hne (hinj heq))
    · simp
  intro j
  apply sum_smul_pow_eq_zero p hp hb (f j)
  apply MvPowerSeries.ext
  intro n
  by_cases hd : ∀ x, p ∣ n x
  · let m : σ →₀ ℕ := n.mapRange (fun a => a / p) (Nat.zero_div p)
    have hn : n = p • m := by
      ext x
      simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply, m]
      exact (Nat.mul_div_cancel' (hd x)).symm
    rw [hn]
    simpa only [map_sum, coeff_smul, coeff_pow_smul p hp, coeff_zero] using hc j m
  · push Not at hd
    obtain ⟨x, hx⟩ := hd
    simp only [map_sum, coeff_smul, coeff_pow_of_not_dvd p hp _ n x hx,
      mul_zero, Finset.sum_const_zero, coeff_zero]

end MvPowerSeries
