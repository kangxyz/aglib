/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.Symbols
public import Aglib.KTheory.MilnorK.K3.PolynomialResidue

/-!
# Reduced multiplication in the actual polynomial degree filtration

The lower stage is the integer span of actual rational-function K₃ symbols
whose three polynomial entries are nonzero and have degree strictly below the
stage. Multiplication of reduced representatives differs from multiplication
of their literal polynomial lifts by an element of this span.

The correction polynomial and all its degree bounds are derived by monic
polynomial division. Steinberg on `(fp/c, aa′/c)` then gives the sign-correct
identity. This constructs neither a finite-extension norm nor rational-function
exactness, and does not replace the original K₂ or K₃ quotient.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.DegreeFiltration

open Polynomial
open PolynomialResidue

variable {k : Type*} [Field k]

/-- Actual three-polynomial symbols strictly below a degree bound. -/
def lowerGenerators (k : Type*) [Field k] (d : ℕ) : Set (Group (RatFunc k)) :=
  {x | ∃ (a b c : k[X]) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0),
    a.natDegree < d ∧ b.natDegree < d ∧ c.natDegree < d ∧
    x = symbol3 (polynomialUnit a ha) (polynomialUnit b hb) (polynomialUnit c hc)}

/-- The lower degree stage in the actual rational-function Milnor K₃ group. -/
def lower (k : Type*) [Field k] (d : ℕ) : Submodule ℤ (Group (RatFunc k)) :=
  Submodule.span ℤ (lowerGenerators k d)

/-- A literal symbol with three smaller-degree polynomial entries lies in the lower stage. -/
theorem polynomial_symbol_mem_lower (d : ℕ) (a b c : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hadeg : a.natDegree < d) (hbdeg : b.natDegree < d) (hcdeg : c.natDegree < d) :
    symbol3 (polynomialUnit a ha) (polynomialUnit b hb) (polynomialUnit c hc) ∈
      lower k d :=
  Submodule.subset_span ⟨a, b, c, ha, hb, hc, hadeg, hbdeg, hcdeg, rfl⟩

/-- The lower stages increase with their degree bounds. -/
theorem lower_mono {d e : ℕ} (hde : d ≤ e) : lower k d ≤ lower k e := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, b, c, ha, hb, hc, hadeg, hbdeg, hcdeg, rfl⟩
  exact polynomial_symbol_mem_lower e a b c ha hb hc
    (hadeg.trans_le hde) (hbdeg.trans_le hde) (hcdeg.trans_le hde)

private theorem polynomialUnit_mul (a a' : k[X]) (ha : a ≠ 0) (ha' : a' ≠ 0) :
    polynomialUnit (a * a') (mul_ne_zero ha ha') =
      polynomialUnit a ha * polynomialUnit a' ha' := by
  apply Units.ext
  exact map_mul (algebraMap k[X] (RatFunc k)) a a'

variable (p : k[X]) [Fact (Irreducible p)]

/-- The remainder of a product of nonzero reduced representatives is nonzero. -/
theorem reduced_mul_ne_zero (hp : p.Monic) (a a' : k[X])
    (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (ha'deg : a'.natDegree < p.natDegree) :
    (a * a') %ₘ p ≠ 0 := by
  intro hzero
  have hdvd := (modByMonic_eq_zero_iff_dvd hp).mp hzero
  rcases (Fact.out : Irreducible p).prime.dvd_mul.mp hdvd with hpa | hpa'
  · exact hp.not_dvd_of_natDegree_lt ha hadeg hpa
  · exact hp.not_dvd_of_natDegree_lt ha' ha'deg hpa'

/-- The product remainder has genuinely smaller degree than the irreducible modulus. -/
theorem reduced_mul_natDegree_lt (hp : p.Monic) (a a' : k[X]) :
    ((a * a') %ₘ p).natDegree < p.natDegree :=
  natDegree_modByMonic_lt (a * a') hp (Fact.out : Irreducible p).ne_one

omit [Fact (Irreducible p)] in
/-- In the nontrivial branch monic division supplies a nonzero smaller-degree correction. -/
theorem reduced_mul_correction (hp : p.Monic) (a a' : k[X])
    (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (ha'deg : a'.natDegree < p.natDegree)
    (hne : a * a' ≠ (a * a') %ₘ p) :
    ∃ f : k[X], f ≠ 0 ∧ f.natDegree < p.natDegree ∧
      (a * a') %ₘ p = a * a' + f * p := by
  refine ⟨-((a * a') /ₘ p), ?_, ?_, ?_⟩
  · intro hf
    have hdiv := neg_eq_zero.mp hf
    have heq := modByMonic_add_div (a * a') p
    rw [hdiv, mul_zero, add_zero] at heq
    exact hne heq.symm
  · rw [natDegree_neg, natDegree_divByMonic _ hp, natDegree_mul ha ha']
    omega
  · have heq := modByMonic_add_div (a * a') p
    calc
      (a * a') %ₘ p = a * a' - p * ((a * a') /ₘ p) := eq_sub_of_add_eq heq
      _ = a * a' + -((a * a') /ₘ p) * p := by ring

private theorem symbol3_correction {K : Type*} [Field K]
    (p a a' b c f : Kˣ) (hsum : (f : K) * p + (a : K) * a' = c) :
    symbol3 p a b + symbol3 p a' b - symbol3 p c b =
      -symbol3 (f / c) (a * a' / c) b := by
  have hnormalized : (((f / c) * p : Kˣ) : K) +
      ((a * a' / c : Kˣ) : K) = 1 := by
    simp only [Units.val_mul, Units.val_div_eq_div_val]
    rw [div_mul_eq_mul_div, ← add_div, hsum, div_self c.ne_zero]
  have hs := symbol3_steinberg_left ((f / c) * p) (a * a' / c) b hnormalized
  rw [symbol3_mul_left, symbol3_div_middle p, symbol3_mul_middle p] at hs
  exact eq_neg_of_add_eq_zero_right hs

/-- Reduced multiplication in the middle coordinate holds modulo the actual lower stage. -/
theorem reduced_mul_middle_mem_lower (hp : p.Monic) (a a' b : k[X])
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (ha'deg : a'.natDegree < p.natDegree)
    (hbdeg : b.natDegree < p.natDegree) :
    symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
        (polynomialUnit a ha) (polynomialUnit b hb) +
      symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
        (polynomialUnit a' ha') (polynomialUnit b hb) -
      symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
        (polynomialUnit ((a * a') %ₘ p) (reduced_mul_ne_zero p hp a a' ha ha' hadeg ha'deg))
        (polynomialUnit b hb) ∈ lower k p.natDegree := by
  have hc := reduced_mul_ne_zero p hp a a' ha ha' hadeg ha'deg
  have hcdeg := reduced_mul_natDegree_lt p hp a a'
  by_cases heq : a * a' = (a * a') %ₘ p
  · have hunit : polynomialUnit ((a * a') %ₘ p) hc =
        polynomialUnit a ha * polynomialUnit a' ha' := by
      rw [← polynomialUnit_mul a a' ha ha']
      congr 1
      exact heq.symm
    rw [hunit, symbol3_mul_middle, sub_self]
    exact (lower k p.natDegree).zero_mem
  · obtain ⟨f, hf, hfdeg, hfeq⟩ := reduced_mul_correction p hp a a' ha ha' hadeg ha'deg heq
    have hsum : (polynomialUnit f hf : RatFunc k) *
          (polynomialUnit p (Fact.out : Irreducible p).ne_zero : RatFunc k) +
        (polynomialUnit a ha : RatFunc k) * (polynomialUnit a' ha' : RatFunc k) =
          (polynomialUnit ((a * a') %ₘ p) hc : RatFunc k) := by
      simpa only [polynomialUnit_coe, map_add, map_mul, add_comm] using
        congrArg (algebraMap k[X] (RatFunc k)) hfeq.symm
    rw [symbol3_correction _ _ _ _ _ _ hsum, symbol3_div_left,
      symbol3_div_middle, symbol3_div_middle, symbol3_mul_middle, symbol3_mul_middle]
    apply (lower k p.natDegree).neg_mem
    apply (lower k p.natDegree).sub_mem
    · exact (lower k p.natDegree).sub_mem
        ((lower k p.natDegree).add_mem
          (polynomial_symbol_mem_lower _ _ _ _ hf ha hb hfdeg hadeg hbdeg)
          (polynomial_symbol_mem_lower _ _ _ _ hf ha' hb hfdeg ha'deg hbdeg))
        (polynomial_symbol_mem_lower _ _ _ _ hf hc hb hfdeg hcdeg hbdeg)
    · exact (lower k p.natDegree).sub_mem
        ((lower k p.natDegree).add_mem
          (polynomial_symbol_mem_lower _ _ _ _ hc ha hb hcdeg hadeg hbdeg)
          (polynomial_symbol_mem_lower _ _ _ _ hc ha' hb hcdeg ha'deg hbdeg))
        (polynomial_symbol_mem_lower _ _ _ _ hc hc hb hcdeg hcdeg hbdeg)

/-- Reduced multiplication in the last coordinate follows with the same lower stage. -/
theorem reduced_mul_right_mem_lower (hp : p.Monic) (a b b' : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (hbdeg : b.natDegree < p.natDegree)
    (hb'deg : b'.natDegree < p.natDegree) :
    symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
        (polynomialUnit a ha) (polynomialUnit b hb) +
      symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
        (polynomialUnit a ha) (polynomialUnit b' hb') -
      symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
        (polynomialUnit a ha)
        (polynomialUnit ((b * b') %ₘ p) (reduced_mul_ne_zero p hp b b' hb hb' hbdeg hb'deg)) ∈
      lower k p.natDegree := by
  have h := (lower k p.natDegree).neg_mem
    (reduced_mul_middle_mem_lower p hp b b' a hb hb' ha hbdeg hb'deg hadeg)
  rw [symbol3_skew_right _ (polynomialUnit a ha) (polynomialUnit b hb),
    symbol3_skew_right _ (polynomialUnit a ha) (polynomialUnit b' hb'),
    symbol3_skew_right _ (polynomialUnit a ha)
      (polynomialUnit ((b * b') %ₘ p) _)]
  convert h using 1
  abel

/-- Reduced representatives summing to one in the residue field already sum to one literally. -/
theorem reduced_add_eq_one (hp : p.Monic) (a b : k[X])
    (hadeg : a.natDegree < p.natDegree) (hbdeg : b.natDegree < p.natDegree)
    (hsum : AdjoinRoot.mk p a + AdjoinRoot.mk p b = 1) : a + b = 1 := by
  have hzero : AdjoinRoot.mk p (a + b - 1) = 0 := by
    rw [map_sub, map_add, map_one, hsum, sub_self]
  have hdeg : (a + b - 1).natDegree < p.natDegree := by
    apply (natDegree_sub_le _ _).trans_lt
    apply max_lt
    · exact (natDegree_add_le _ _).trans_lt (max_lt hadeg hbdeg)
    · simpa only [natDegree_one] using (Nat.zero_le a.natDegree).trans_lt hadeg
  by_contra hne
  exact hp.not_dvd_of_natDegree_lt (sub_ne_zero.mpr hne) hdeg
    (AdjoinRoot.mk_eq_zero.mp hzero)

/-- Residue-field Steinberg on reduced representatives vanishes in the actual K₃ group. -/
theorem reduced_steinberg (hp : p.Monic) (a b : k[X])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hadeg : a.natDegree < p.natDegree) (hbdeg : b.natDegree < p.natDegree)
    (hsum : AdjoinRoot.mk p a + AdjoinRoot.mk p b = 1) :
    symbol3 (polynomialUnit p (Fact.out : Irreducible p).ne_zero)
      (polynomialUnit a ha) (polynomialUnit b hb) = 0 := by
  apply symbol3_steinberg_right
  have heq := reduced_add_eq_one p hp a b hadeg hbdeg hsum
  simpa only [polynomialUnit_coe, map_add, map_one] using
    congrArg (algebraMap k[X] (RatFunc k)) heq

end MilnorK.K3.DegreeFiltration
