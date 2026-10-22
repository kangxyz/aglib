/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Valuation.LeadingResidues
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Frobenius independence from leading residues
-/

@[expose] public noncomputable section

open scoped BigOperators
open WithZero

namespace Valuation

variable {L : Type*} [Field L] (v : Valuation L ℤᵐ⁰)

/-- The discrete arithmetic in the leading-term argument. The bounds on both
orders are essential: they force the normalized Frobenius root to be integral,
and make every different order class disappear in the residue field. -/
theorem frobenius_leading_bound (p : ℕ) (hp : 0 < p)
    (r s : ℤ) (hr0 : 0 ≤ r) (hrp : r < p) (hs0 : 0 ≤ s) (hsp : s < p)
    (x : L) (h : v x ^ p * exp (s - r) ≤ 1) :
    v x ≤ 1 ∧ (r ≠ s → v x ^ p * exp (s - r) < 1) := by
  by_cases hx : x = 0
  · simp [hx, Nat.ne_of_gt hp]
  have hvx : v x ≠ 0 := by simpa using hx
  let n : ℤ := log (v x)
  have hval : v x ^ p * exp (s - r) = exp ((p : ℤ) * n + s - r) := by
    rw [← exp_log hvx, ← exp_nsmul, ← exp_add]
    congr 1
    simp only [n, nsmul_eq_mul]
    ring
  have hnum : (p : ℤ) * n + s - r ≤ 0 := by
    rw [hval, ← exp_zero, exp_le_exp] at h
    exact h
  have hn : n ≤ 0 := by
    by_contra hn
    have hn1 : 1 ≤ n := by omega
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [← exp_log hvx, ← exp_zero, exp_le_exp]
    exact hn
  intro hrs
  rw [hval, ← exp_zero, exp_lt_exp]
  by_cases hn0 : n = 0
  · have : s < r := by
      rw [hn0, mul_zero, zero_add] at hnum
      omega
    simpa only [hn0, mul_zero, zero_add, sub_neg] using this
  · have hn1 : n ≤ -1 := by omega
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
    nlinarith

/-- A finite family with distinct-order groups having independent leading
residues is independent over the literal Frobenius subfield. This theorem
contains the minimum-valuation argument; it assumes neither completeness nor
any a priori independence over the ambient field. -/
theorem linearIndependent_frobenius_of_leadingResidues
    {ι : Type*} [Finite ι] (p : ℕ) (hp : 0 < p) [ExpChar L p]
    [ExpChar (IsLocalRing.ResidueField v.valuationSubring) p]
    (π : L) (hπ : v π = exp (-1))
    (b : ι → L) (r : ι → ℤ)
    (hr0 : ∀ i, 0 ≤ r i) (hrp : ∀ i, r i < p)
    (hb : ∀ i, v (b i) = exp (-r i))
    (hres : ∀ s : ℤ,
      LinearIndependent
        (frobenius (IsLocalRing.ResidueField v.valuationSubring) p).fieldRange
        (fun i : {i // r i = s} => IsLocalRing.residue v.valuationSubring
          (v.leadingInteger π hπ s (b i) (by simpa only [i.property] using hb i)))) :
    LinearIndependent (frobenius L p).fieldRange b := by
  classical
  let := Fintype.ofFinite ι
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  by_contra hcz
  obtain ⟨i₁, hi₁⟩ := not_forall.mp hcz
  have hroots : ∀ i, ∃ a : L, a ^ p = (c i : L) := by
    intro i
    simpa only [RingHom.mem_fieldRange, frobenius_def] using (c i).property
  choose a ha using hroots
  have ha₁ : a i₁ ≠ 0 := by
    intro hh
    apply hi₁
    apply Subtype.ext
    change (c i₁ : L) = 0
    rw [← ha i₁, hh, zero_pow (Nat.ne_of_gt hp)]
  let term (i : ι) : L := a i ^ p * b i
  have hb0 (i : ι) : b i ≠ 0 := by
    intro hh
    have : (exp (-r i) : ℤᵐ⁰) = 0 := by simpa only [hh, map_zero] using (hb i).symm
    exact exp_ne_zero this
  have ht₁ : v (term i₁) ≠ 0 := by
    exact v.ne_zero_iff.mpr (mul_ne_zero (pow_ne_zero p ha₁) (hb0 i₁))
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => v (term i))
    ⟨i₁, Finset.mem_univ _⟩
  have ht₀ : v (term i₀) ≠ 0 := by
    intro hh
    exact ht₁ (le_zero_iff.mp (hh ▸ hmax i₁ (Finset.mem_univ _)))
  have ha₀ : a i₀ ≠ 0 := by
    intro hh
    apply ht₀
    simp [term, hh, Nat.ne_of_gt hp]
  have hπ0 : π ≠ 0 := by
    intro hh
    exact exp_ne_zero (by simpa only [hh, map_zero] using hπ.symm)
  let s : ℤ := r i₀
  let den : L := a i₀ ^ p * π ^ s
  have hden0 : den ≠ 0 := mul_ne_zero (pow_ne_zero _ ha₀) (zpow_ne_zero _ hπ0)
  have hden : v den = v (term i₀) := by
    simp only [den, term, map_mul, map_pow, map_zpow₀, hπ, hb, s]
    congr 1
    rw [← exp_zsmul]
    simp only [zsmul_eq_mul, Int.cast_id, mul_neg, mul_one]
  let t (i : ι) : L := term i / den
  have ht (i : ι) : v (t i) ≤ 1 := by
    dsimp only [t]
    rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr (by simpa using hden0)), hden]
    exact hmax i (Finset.mem_univ _)
  let d (i : ι) : L := a i / a i₀
  have htform (i : ι) : t i = d i ^ p * (b i * π ^ (-s)) := by
    dsimp only [t, term, den, d]
    rw [div_pow, zpow_neg]
    field_simp
  have htval (i : ι) : v (t i) = v (d i) ^ p * exp (s - r i) := by
    rw [htform, map_mul, map_pow, map_mul, hb, map_zpow₀, hπ,
      ← exp_zsmul, ← exp_add]
    congr 2
    simp only [zsmul_eq_mul, Int.cast_id]
    ring
  have hdi (i : ι) : v (d i) ≤ 1 ∧ (r i ≠ s → v (t i) < 1) := by
    have hh := v.frobenius_leading_bound p hp (r i) s (hr0 i) (hrp i)
      (hr0 i₀) (hrp i₀) (d i) (by simpa only [← htval] using ht i)
    simpa only [← htval] using hh
  let A := v.valuationSubring
  let k := IsLocalRing.ResidueField A
  let ρ : A →+* k := IsLocalRing.residue A
  let D (i : ι) : A := ⟨d i, (hdi i).1⟩
  let T (i : ι) : A := ⟨t i, ht i⟩
  have hsumT : ∑ i, T i = 0 := by
    apply Subtype.ext
    change A.subtype (∑ i, T i) = A.subtype 0
    rw [map_sum, map_zero]
    change ∑ i, term i / den = 0
    rw [← Finset.sum_div]
    have hc' : ∑ i, term i = 0 := by
      change ∑ i, (c i : L) * b i = 0 at hc
      simpa only [term, ha] using hc
    rw [hc', zero_div]
  have hresT (i : ι) (hi : r i ≠ s) : ρ (T i) = 0 := by
    exact (IsLocalRing.residue_eq_zero_iff (T i)).mpr
      (v.mem_maximalIdeal_iff.mpr ((hdi i).2 hi))
  let J := {i // r i = s}
  let β (i : J) : A := v.leadingInteger π hπ s (b i)
    (by simpa only [i.property] using hb i)
  have hTi (i : J) : T i = D i ^ p * β i := by
    apply Subtype.ext
    exact htform i
  have hresSum : ∑ i : J, ρ (D i) ^ p * ρ (β i) = 0 := by
    have hh := congrArg ρ hsumT
    rw [map_sum, map_zero] at hh
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => r i = s)
      (fun i => ρ (T i))] at hh
    have hz : (∑ i : {i // ¬r i = s}, ρ (T i)) = 0 :=
      Finset.sum_eq_zero (fun i hi => hresT i i.property)
    rw [hz, add_zero] at hh
    simpa only [hTi, map_mul, map_pow] using hh
  let C (i : J) : (frobenius k p).fieldRange :=
    (frobenius k p).rangeRestrictField (ρ (D i))
  have hC : ∀ i : J, C i = 0 := by
    apply Fintype.linearIndependent_iff.mp (hres s) C
    exact hresSum
  have hD₀ : D i₀ = 1 := by
    apply Subtype.ext
    exact div_self ha₀
  have hbad := congrArg Subtype.val (hC ⟨i₀, rfl⟩)
  change ρ (D i₀) ^ p = 0 at hbad
  rw [hD₀, map_one, one_pow] at hbad
  exact one_ne_zero hbad

end Valuation
