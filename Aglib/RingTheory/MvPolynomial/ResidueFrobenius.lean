/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.FrobeniusCoefficients
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Frobenius independence of rational monomials

Finite coefficient independence and distinct exponent residues imply independence
of coefficient-times-monomial families over the literal rational Frobenius range.
The proof clears actual rational denominators and reuses coefficient comparison.
-/

@[expose] public noncomputable section

namespace MvPolynomial

/-- Rational p-th-power relations between bounded monomials vanish termwise.
The fraction field and its polynomial algebra map are supplied explicitly. -/
lemma sum_monomial_mul_pow_eq_zero_fractionRing
    {k G σ ι ρ : Type*} [Field k] [Field G]
    [Algebra (MvPolynomial σ k) G] [IsFractionRing (MvPolynomial σ k) G]
    [Fintype ι] [Fintype ρ]
    (p : ℕ) (hp : p ≠ 0) [ExpChar k p]
    {b : ι → k} (hb : LinearIndependent (frobenius k p).fieldRange b)
    (r : ρ → σ →₀ ℕ) (hr : ∀ e x, r e x < p) (hinj : Function.Injective r)
    (g : ρ → ι → G)
    (h : ∑ e, ∑ j, algebraMap (MvPolynomial σ k) G (monomial (r e) (b j)) *
      g e j ^ p = 0) : ∀ e j, g e j = 0 := by
  classical
  let m := algebraMap (MvPolynomial σ k) G
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (MvPolynomial σ k)) (fun q : ρ × ι => g q.1 q.2)
  choose f hf using ha
  have hf' (q : ρ × ι) : m (f q) = m (a : MvPolynomial σ k) * g q.1 q.2 := by
    simpa only [Algebra.smul_def] using hf q
  have ha0 : m (a : MvPolynomial σ k) ≠ 0 := by
    intro hz
    apply mem_nonZeroDivisors_iff_ne_zero.mp a.property
    apply IsFractionRing.injective (MvPolynomial σ k) G
    simpa only [map_zero] using hz
  have hpoly : ∑ e, ∑ j, monomial (r e) (b j) * f (e, j) ^ p = 0 := by
    apply IsFractionRing.injective (MvPolynomial σ k) G
    rw [map_zero]
    calc
      m (∑ e, ∑ j, monomial (r e) (b j) * f (e, j) ^ p) =
          m (a : MvPolynomial σ k) ^ p *
            (∑ e, ∑ j, m (monomial (r e) (b j)) * g e j ^ p) := by
        simp only [map_sum, map_mul, map_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro j hj
        rw [hf' (e, j), mul_pow]
        ring
      _ = 0 := by rw [h, mul_zero]
  have hseries := congrArg
    (coeToMvPowerSeries.ringHom : MvPolynomial σ k →+* MvPowerSeries σ k) hpoly
  simp only [map_sum, map_mul, map_pow, map_zero,
    coeToMvPowerSeries.ringHom_apply, coe_monomial] at hseries
  have hfzero := MvPowerSeries.sum_monomial_mul_pow_eq_zero p hp hb r hr hinj
    (fun e j => (f (e, j) : MvPowerSeries σ k)) hseries
  intro e j
  have hf0 : f (e, j) = 0 := coe_eq_zero_iff.mp (hfzero e j)
  have hz : m (a : MvPolynomial σ k) * g e j = 0 := by
    rw [← hf' (e, j), hf0, map_zero]
  exact (mul_eq_zero.mp hz).resolve_left ha0

/-- The finite rational residue-field monomial family is independent over
its literal Frobenius field range. The coefficients need only finite independence. -/
lemma linearIndependent_monomial_fractionRing_frobeniusFieldRange
    {k G σ ι ρ : Type*} [Field k] [Field G]
    [Algebra (MvPolynomial σ k) G] [IsFractionRing (MvPolynomial σ k) G]
    [Finite ι] [Finite ρ]
    (p : ℕ) (hp : p ≠ 0) [ExpChar k p] [ExpChar G p]
    {b : ι → k} (hb : LinearIndependent (frobenius k p).fieldRange b)
    (r : ρ → σ →₀ ℕ) (hr : ∀ e x, r e x < p) (hinj : Function.Injective r) :
    LinearIndependent (frobenius G p).fieldRange
      (fun q : ρ × ι => algebraMap (MvPolynomial σ k) G (monomial (r q.1) (b q.2))) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite ρ
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let g (e : ρ) (j : ι) : G :=
    (frobenius G p).rangeRestrictFieldEquiv.symm (c (e, j))
  have hg (e : ρ) (j : ι) : g e j ^ p = (c (e, j) : G) :=
    (frobenius G p).rangeRestrictFieldEquiv_apply_symm_apply (c (e, j))
  have hrel : ∑ e, ∑ j,
      algebraMap (MvPolynomial σ k) G (monomial (r e) (b j)) * g e j ^ p = 0 := by
    change ∑ q : ρ × ι, (c q : G) *
      algebraMap (MvPolynomial σ k) G (monomial (r q.1) (b q.2)) = 0 at hc
    simpa only [Fintype.sum_prod_type, hg, mul_comm] using hc
  have hg0 := sum_monomial_mul_pow_eq_zero_fractionRing p hp hb r hr hinj g hrel
  rintro ⟨e, j⟩
  apply Subtype.ext
  change (c (e, j) : G) = 0
  rw [← hg e j, hg0 e j, zero_pow hp]

end MvPolynomial
