/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Valuation.Orthogonal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Normalization and leading residues of finite Frobenius-orthogonal families.
-/

@[expose] public noncomputable section

open scoped BigOperators
open WithZero

namespace Valuation

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)

/-- Common multiplication by an ambient scalar preserves orthogonality, even when
that scalar is not in the coefficient field. -/
theorem IsOrthogonal.mul_const (E : Subfield K) {ι : Type*} [Fintype ι]
    {b : ι → K} (hb : v.IsOrthogonal E b) (a : K) :
    v.IsOrthogonal E (fun i => b i * a) := by
  intro c i
  have h := mul_le_mul_of_nonneg_right (hb c i) (zero_le : (0 : ℤᵐ⁰) ≤ v a)
  simpa only [← map_mul, Finset.sum_mul, mul_assoc] using h

/-- Unit-valued orthogonal families have Frobenius-independent residues.
This uses the literal valuation ring and its literal residue map. The proof
lifts roots of residue coefficients, not arbitrary coefficients as roots. -/
theorem IsOrthogonal.linearIndependent_residue
    {ι : Type*} [Fintype ι] (p : ℕ) [ExpChar K p]
    [ExpChar (IsLocalRing.ResidueField v.valuationSubring) p]
    (b : ι → v.valuationSubring)
    (hb : v.IsOrthogonal (frobenius K p).fieldRange (fun i => (b i : K)))
    (hbval : ∀ i, v (b i : K) = 1) :
    LinearIndependent
      (frobenius (IsLocalRing.ResidueField v.valuationSubring) p).fieldRange
      (fun i => IsLocalRing.residue v.valuationSubring (b i)) := by
  classical
  let A := v.valuationSubring
  let k := IsLocalRing.ResidueField A
  let ρ : A →+* k := IsLocalRing.residue A
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hroots : ∀ i, ∃ t : k, t ^ p = (c i : k) := by
    intro i
    simpa only [RingHom.mem_fieldRange, frobenius_def] using (c i).property
  choose t ht using hroots
  choose a ha using fun i => (IsLocalRing.residue_surjective (t i))
  let d (i : ι) : (frobenius K p).fieldRange :=
    (frobenius K p).rangeRestrictField (a i : K)
  let z : A := ∑ i, a i ^ p * b i
  have hzres : ρ z = 0 := by
    change ∑ i, (c i : k) * ρ (b i) = 0 at hc
    simpa only [z, map_sum, map_mul, map_pow, ρ, ha, ht] using hc
  have hzval : v (z : K) < 1 :=
    v.mem_maximalIdeal_iff.mp ((IsLocalRing.residue_eq_zero_iff z).mp hzres)
  have hsum : (∑ i, ((d i : (frobenius K p).fieldRange) : K) * (b i : K)) =
      (z : K) := by
    change (∑ i, ((d i : (frobenius K p).fieldRange) : K) * A.subtype (b i)) =
      A.subtype (∑ i, a i ^ p * b i)
    simp only [d, RingHom.coe_rangeRestrictField, frobenius_def,
      map_sum, map_mul, map_pow, ValuationSubring.subtype_apply]
  have hzsum : v (∑ i, ((d i : (frobenius K p).fieldRange) : K) * (b i : K)) < 1 := by
    rw [hsum]
    exact hzval
  intro i
  have hi := (hb d i).trans_lt hzsum
  have hpow : v (a i : K) ^ p < 1 := by
    simpa only [d, RingHom.coe_rangeRestrictField, frobenius_def,
      map_mul, map_pow, hbval i, mul_one] using hi
  have hsmall : v (a i : K) < 1 :=
    lt_of_pow_lt_pow_left₀ p zero_le_one (by simpa only [one_pow] using hpow)
  have ha0 : ρ (a i) = 0 :=
    (IsLocalRing.residue_eq_zero_iff (a i)).mpr (v.mem_maximalIdeal_iff.mpr hsmall)
  apply Subtype.ext
  change (c i : k) = 0
  rw [← ht i, ← ha i, ha0]
  exact zero_pow (expChar_ne_zero K p)

/-- Normalize a nonzero vector by a coefficient in the literal Frobenius field.
The integer `r` is its additive valuation modulo `p`. -/
theorem exists_frobenius_normalization (p : ℕ) [ExpChar K p] (hp : 0 < p)
    (π : K) (hπ : v π = exp (-1)) {b : K} (hb : b ≠ 0) :
    ∃ a : (frobenius K p).fieldRange, a ≠ 0 ∧
      ∃ r : ℤ, 0 ≤ r ∧ r < p ∧ v ((a : K) * b) = exp (-r) := by
  classical
  let m : ℤ := -log (v b)
  let q : ℤ := m / (p : ℤ)
  let r : ℤ := m % (p : ℤ)
  let a : (frobenius K p).fieldRange :=
    (frobenius K p).rangeRestrictField (π ^ (-q))
  have hπ0 : π ≠ 0 := by
    intro h
    have hz : (exp (-1) : ℤᵐ⁰) = 0 := by
      simpa only [h, map_zero] using hπ.symm
    exact exp_ne_zero hz
  have ha : a ≠ 0 := by
    intro h
    have hz := congrArg Subtype.val h
    exact pow_ne_zero p (zpow_ne_zero _ hπ0) hz
  refine ⟨a, ha, r, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega), ?_⟩
  have hdecomp : m = (p : ℤ) * q + r := by
    exact (Int.mul_ediv_add_emod m (p : ℤ)).symm
  have hvb0 : v b ≠ 0 := by simpa using hb
  have hvb : v b = exp (-m) := by
    change v b = exp (-(-log (v b)))
    rw [neg_neg]
    exact (exp_log hvb0).symm
  change v ((π ^ (-q)) ^ p * b) = exp (-r)
  rw [map_mul, map_pow, map_zpow₀, hπ, hvb, ← exp_zsmul, ← exp_nsmul, ← exp_add]
  congr 1
  simp only [zsmul_eq_mul, nsmul_eq_mul, Int.cast_id]
  linear_combination -hdecomp

/-- A finite Frobenius coefficient space admits a basis normalized by valuation modulo p. -/
theorem exists_normalized_frobenius_orthogonal_span (hK : v.IsSeqComplete)
    (p : ℕ) [ExpChar K p] (hp : 0 < p) (π : K) (hπ : v π = exp (-1))
    (W : Submodule (frobenius K p).fieldRange K) [Module.Finite (frobenius K p).fieldRange W] :
    ∃ n : ℕ, ∃ b : Fin n → K, ∃ r : Fin n → ℤ,
      LinearIndependent (frobenius K p).fieldRange b ∧
      Submodule.span (frobenius K p).fieldRange (Set.range b) = W ∧
      v.IsOrthogonal (frobenius K p).fieldRange b ∧
      ∀ i, 0 ≤ r i ∧ r i < p ∧ v (b i) = exp (-r i) := by
  classical
  obtain ⟨n, b, hli, hspan, hb⟩ :=
    v.exists_frobenius_orthogonal_span hK p hp W
  have hnorm := fun i => v.exists_frobenius_normalization p hp π hπ (hli.ne_zero i)
  choose a ha r hr0 hrp hr using hnorm
  refine ⟨n, (fun i => (a i : K) * b i), r, ?_, ?_, Valuation.IsOrthogonal.mul v _ hb a, ?_⟩
  · have hscaled := hli.units_smul (fun i => Units.mk0 (a i) (ha i))
    have heq : ((fun i => Units.mk0 (a i) (ha i)) • b) =
        (fun i => (a i : K) * b i) := by
      funext i
      rfl
    rw [heq] at hscaled
    exact hscaled
  · rw [Valuation.span_mul_eq _ b a ha, hspan]
  · exact fun i => ⟨hr0 i, hrp i, hr i⟩

/-- Dividing a vector of additive order r by π^r gives a valuation-one element. -/
theorem valuation_leading_one (π : K) (hπ : v π = exp (-1))
    (r : ℤ) (b : K) (hb : v b = exp (-r)) : v (b * π ^ (-r)) = 1 := by
  rw [map_mul, map_zpow₀, hb, hπ, ← exp_zsmul, ← exp_add]
  have h : -r + (-r) • (-1 : ℤ) = 0 := by simp
  rw [h, exp_zero]

/-- The actual integral representative used to take a leading residue. -/
def leadingInteger (π : K) (hπ : v π = exp (-1))
    (r : ℤ) (b : K) (hb : v b = exp (-r)) : v.valuationSubring :=
  ⟨b * π ^ (-r), (v.valuation_leading_one π hπ r b hb).le⟩

/-- Leading residues in each fixed valuation class are Frobenius-independent.
No independence between different valuation classes is asserted. -/
theorem IsOrthogonal.linearIndependent_leadingResidues
    {ι : Type*} [Fintype ι] (p : ℕ) [ExpChar K p]
    [ExpChar (IsLocalRing.ResidueField v.valuationSubring) p]
    (π : K) (hπ : v π = exp (-1)) {b : ι → K}
    (hb : v.IsOrthogonal (frobenius K p).fieldRange b)
    (r : ι → ℤ) (hval : ∀ i, v (b i) = exp (-r i)) (s : ℤ) :
    LinearIndependent
      (frobenius (IsLocalRing.ResidueField v.valuationSubring) p).fieldRange
      (fun i : {i // r i = s} => IsLocalRing.residue v.valuationSubring
        (v.leadingInteger π hπ s (b i) (by simpa only [i.property] using hval i))) := by
  classical
  let β (i : {i // r i = s}) : v.valuationSubring :=
    v.leadingInteger π hπ s (b i) (by simpa only [i.property] using hval i)
  apply Valuation.IsOrthogonal.linearIndependent_residue v p β
  · exact Valuation.IsOrthogonal.mul_const v _
      (Valuation.IsOrthogonal.subtype v _ hb (fun i => r i = s)) (π ^ (-s))
  · intro i
    exact v.valuation_leading_one π hπ s (b i)
      (by simpa only [i.property] using hval i)

end Valuation
