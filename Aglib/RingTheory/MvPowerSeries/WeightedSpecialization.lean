/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Data.Finsupp.Weight

/-!
# Coefficients of weighted specialization

Substitution of positive powers of one variable is a genuine formal
substitution. Its coefficient of degree `k` is the finite sum of the original
coefficients of weight `k`. In particular, a uniquely least-weight nonzero
coefficient survives specialization over any commutative ring. No division,
characteristic restriction, or infinitude of the coefficient ring is used.
-/

@[expose] public section

namespace MvPowerSeries

variable {R σ τ : Type*} [CommRing R] [Finite σ]

lemma hasSubst_X_pow_weight (p : τ) (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    HasSubst (fun i ↦ (X p : MvPowerSeries τ R) ^ w i) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  simp [(hw i).ne']

omit [Finite σ] in
lemma prod_X_pow_weight (p : τ) (w : σ → ℕ) (d : σ →₀ ℕ) :
    (d.prod fun i n ↦ ((X p : MvPowerSeries τ R) ^ w i) ^ n) =
      X p ^ Finsupp.weight w d := by
  classical
  simp only [Finsupp.prod, ← pow_mul, Finset.prod_pow_eq_pow_sum,
    Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_comm]

/-- The coefficient of a weighted specialization is the sum over its weight fiber. -/
theorem coeff_subst_X_pow_weight (p : τ) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (f : MvPowerSeries σ R) (k : ℕ) :
    coeff (Finsupp.single p k) (subst (fun i ↦ (X p : MvPowerSeries τ R) ^ w i) f) =
      ∑ᶠ d : σ →₀ ℕ, if Finsupp.weight w d = k then coeff d f else 0 := by
  classical
  rw [coeff_subst (hasSubst_X_pow_weight p w hw)]
  apply finsum_congr
  intro d
  rw [prod_X_pow_weight, coeff_X_pow]
  simp only [(Finsupp.single_injective p).eq_iff, smul_eq_mul, mul_ite,
    mul_one, mul_zero, eq_comm]

/-- A coefficient isolated from the rest of the support by its weight survives. -/
theorem coeff_subst_X_pow_weight_eq_of_isolated (p : τ) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (f : MvPowerSeries σ R) (a : σ →₀ ℕ)
    (ha : ∀ d, d ≠ a → coeff d f ≠ 0 → Finsupp.weight w a < Finsupp.weight w d) :
    coeff (Finsupp.single p (Finsupp.weight w a))
      (subst (fun i ↦ (X p : MvPowerSeries τ R) ^ w i) f) = coeff a f := by
  classical
  rw [coeff_subst_X_pow_weight p w hw, finsum_eq_single _ a]
  · simp
  · intro d hd
    by_cases hdf : coeff d f = 0
    · simp [hdf]
    · simp [(ne_of_gt (ha d hd hdf))]

/-- All coefficients below an isolated least weight vanish after specialization. -/
theorem coeff_subst_X_pow_weight_eq_zero_of_lt (p : τ) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (f : MvPowerSeries σ R) (a : σ →₀ ℕ)
    (ha : ∀ d, d ≠ a → coeff d f ≠ 0 → Finsupp.weight w a < Finsupp.weight w d)
    (k : ℕ) (hk : k < Finsupp.weight w a) :
    coeff (Finsupp.single p k)
      (subst (fun i ↦ (X p : MvPowerSeries τ R) ^ w i) f) = 0 := by
  classical
  rw [coeff_subst_X_pow_weight p w hw]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hdf : coeff d f = 0
  · simp [hdf]
  · by_cases hd : d = a
    · subst d
      simp [ne_of_gt hk]
    · simp [ne_of_gt (hk.trans (ha d hd hdf))]

end MvPowerSeries
