/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.Coordinates
public import Aglib.RingTheory.Henselian.Quadratic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Henselian lifts of Weierstrass critical points

An actual critical residue point with invertible Hessian lifts over a Henselian
local ring. The resulting admissible translation has vanishing linear terms
and preserves the original discriminant, in every residue characteristic.
-/

@[expose] public noncomputable section

open Polynomial
open scoped Polynomial
universe u

open IsLocalRing WeierstrassCurve

namespace WeierstrassCurve.CriticalPoint

variable {R : Type u} [CommRing R]

/-- The exact discriminant factor after moving the critical point to the origin.
This is polynomial algebra, valid in every residue characteristic. -/
theorem discriminant_critical_factor (W : WeierstrassCurve R) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    W.Δ = W.a₆ * -(W.b₂ ^ 3 + 432 * W.a₆) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, h3, h4]
  ring

/-- A split ordinary node has unit quadratic discriminant. With nonunit
constant term, the actual residual factor of the discriminant is a unit. -/
theorem critical_factor_isUnit [IsLocalRing R] (W : WeierstrassCurve R)
    (hb : IsUnit W.b₂) (ha : ¬ IsUnit W.a₆) :
    IsUnit (W.b₂ ^ 3 + 432 * W.a₆) := by
  by_contra h
  have hn : -(432 * W.a₆) ∈ nonunits R := by
    intro hu
    have hu' : IsUnit (432 * W.a₆) := by simpa only [neg_neg] using hu.neg
    exact ha (isUnit_of_mul_isUnit_right hu')
  have hh := IsLocalRing.nonunits_add h hn
  have he : W.b₂ ^ 3 + 432 * W.a₆ + -(432 * W.a₆) = W.b₂ ^ 3 := by ring
  rw [he] at hh
  exact hh (hb.pow 3)

/-- The actual normalized valuation of Delta equals that of the critical
constant term. Constructing the critical lift/formal node coordinates is a
separate geometric obligation, not assumed by a component-count certificate. -/
theorem discriminant_critical_valuation [IsDomain R] [IsDiscreteValuationRing R]
    (W : WeierstrassCurve R)
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0)
    (hb : IsUnit W.b₂) (ha : ¬ IsUnit W.a₆) :
    IsDiscreteValuationRing.addVal R W.Δ = IsDiscreteValuationRing.addVal R W.a₆ := by
  rw [discriminant_critical_factor W h3 h4, AddValuation.map_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (critical_factor_isUnit W hb ha).neg,
    add_zero]
/-- Unit quadratic discriminant gives an elimination coefficient that is a unit,
including residue characteristic two. -/
theorem two_or_a1_isUnit [IsLocalRing R] (W : WeierstrassCurve R)
    (hb : IsUnit W.b₂) : IsUnit (2 : R) ∨ IsUnit W.a₁ := by
  by_contra h
  obtain ⟨h2, h1⟩ := not_or.mp h
  suffices hn : W.b₂ ∈ nonunits R from hn hb
  change W.a₁ ^ 2 + 4 * W.a₂ ∈ nonunits R
  apply IsLocalRing.nonunits_add
  · intro hu
    exact h1 (by simpa using hu)
  · intro hu
    have he : (4 : R) * W.a₂ = 2 * (2 * W.a₂) := by ring
    exact h2 (isUnit_of_mul_isUnit_left (he ▸ hu))

/-- Solve the actual two Weierstrass critical equations near the residue origin.
No smoothness, discriminant valuation, component count, or model identification
is used. The only lifting theorem is mathlib's monic univariate Hensel lemma. -/
theorem exists_critical_origin [HenselianLocalRing R] (W : WeierstrassCurve R)
    (h3 : W.a₃ ∈ maximalIdeal R) (h4 : W.a₄ ∈ maximalIdeal R)
    (hb : IsUnit W.b₂) :
    ∃ r t : R, r ∈ maximalIdeal R ∧ t ∈ maximalIdeal R ∧
      W.a₁ * t - (3 * r ^ 2 + 2 * W.a₂ * r + W.a₄) = 0 ∧
      2 * t + W.a₁ * r + W.a₃ = 0 := by
  rcases two_or_a1_isUnit W hb with h2 | h1
  · have hc : W.a₁ * W.a₃ + 2 * W.a₄ ∈ maximalIdeal R :=
      (maximalIdeal R).add_mem ((maximalIdeal R).mul_mem_left _ h3)
        ((maximalIdeal R).mul_mem_left _ h4)
    obtain ⟨r, hr, hrm⟩ := HenselianLocalRing.exists_quadratic_root_mem_maximalIdeal 6 W.b₂
      (W.a₁ * W.a₃ + 2 * W.a₄) hb hc
    have h2u := h2
    obtain ⟨v, hv⟩ := h2
    let t : R := -(W.a₁ * r + W.a₃) * ↑v⁻¹
    have hi : (2 : R) * ↑v⁻¹ = 1 := hv ▸ v.mul_inv
    have htm : t ∈ maximalIdeal R :=
      (maximalIdeal R).mul_mem_right _ ((maximalIdeal R).neg_mem
        ((maximalIdeal R).add_mem ((maximalIdeal R).mul_mem_left _ hrm) h3))
    have hy : 2 * t + W.a₁ * r + W.a₃ = 0 := by
      dsimp [t]
      linear_combination -(W.a₁ * r + W.a₃) * hi
    refine ⟨r, t, hrm, htm, ?_, hy⟩
    apply h2u.mul_left_cancel
    simp only [mul_zero]
    dsimp [WeierstrassCurve.b₂] at hr
    linear_combination W.a₁ * hy - hr
  · let b : R := 12 * W.a₃ - W.a₁ * W.b₂
    let c : R := 3 * W.a₃ ^ 2 - 2 * W.a₂ * W.a₃ * W.a₁ + W.a₄ * W.a₁ ^ 2
    have hbu : IsUnit b := by
      have he : b = -(W.a₁ * W.b₂) + 12 * W.a₃ := by dsimp [b]; ring
      rw [he]
      exact IsLocalRing.isUnit_add_of_mem_maximalIdeal _ _ (h1.mul hb).neg ((maximalIdeal
        R).mul_mem_left _ h3)
    have hcm : c ∈ maximalIdeal R := by
      apply (residue_eq_zero_iff _).mp
      have hr3 := (residue_eq_zero_iff _).mpr h3
      have hr4 := (residue_eq_zero_iff _).mpr h4
      simp [c, map_sub, map_add, map_mul, map_pow, hr3, hr4]
    obtain ⟨t, ht, htm⟩ := HenselianLocalRing.exists_quadratic_root_mem_maximalIdeal 12 b c hbu hcm
    have h1u := h1
    obtain ⟨v, hv⟩ := h1
    let r : R := -(2 * t + W.a₃) * ↑v⁻¹
    have hi : W.a₁ * ↑v⁻¹ = 1 := hv ▸ v.mul_inv
    have hrm : r ∈ maximalIdeal R :=
      (maximalIdeal R).mul_mem_right _ ((maximalIdeal R).neg_mem
        ((maximalIdeal R).add_mem ((maximalIdeal R).mul_mem_left _ htm) h3))
    have hy : 2 * t + W.a₁ * r + W.a₃ = 0 := by
      dsimp [r]
      linear_combination -(2 * t + W.a₃) * hi
    refine ⟨r, t, hrm, htm, ?_, hy⟩
    apply (h1u.pow 2).mul_left_cancel
    simp only [mul_zero]
    dsimp [b, c, WeierstrassCurve.b₂] at ht
    linear_combination (-3 * (W.a₁ * r - (2 * t + W.a₃)) - 2 * W.a₂ * W.a₁) * hy - ht
/-- The translated polynomial is the actual substitution in the original
Weierstrass equation, rather than a separately supplied curve. -/
theorem translate_polynomial_eval (W : WeierstrassCurve R) (r t x y : R) :
    (translate W r t).toAffine.polynomial.evalEval x y =
      W.toAffine.polynomial.evalEval (x + r) (y + t) := by
  simp [WeierstrassCurve.Affine.evalEval_polynomial, translate_a1, translate_a2,
    translate_a3, translate_a4, translate_a6]
  ring

/-- Determinant of the Jacobian of the two actual critical equations at x:
the Hessian matrix is [[−6x−2a₂, a₁], [a₁, 2]]. -/
def criticalHessianDet (W : WeierstrassCurve R) (x : R) : R :=
  (-6 * x - 2 * W.a₂) * 2 - W.a₁ * W.a₁

/-- Identification with the determinant of the formal Jacobian of mathlib's
actual Weierstrass partial-derivative polynomials. In the first column we fix
Y and differentiate in X; in the second column we differentiate in Y. -/
theorem criticalHessianDet_eq_jacobian (W : WeierstrassCurve R) (x y : R) :
    criticalHessianDet W x =
      ((W.toAffine.polynomialX.eval (C y)).derivative.eval x) *
        (W.toAffine.polynomialY.derivative.evalEval x y) -
      (W.toAffine.polynomialX.derivative.evalEval x y) *
        ((W.toAffine.polynomialY.eval (C y)).derivative.eval x) := by
  simp [criticalHessianDet, WeierstrassCurve.Affine.polynomialX,
    WeierstrassCurve.Affine.polynomialY, Polynomial.evalEval,
    derivative_pow, derivative_mul]
  ring

theorem criticalHessianDet_eq (W : WeierstrassCurve R) (x : R) :
    criticalHessianDet W x = -(W.b₂ + 12 * x) := by
  simp [criticalHessianDet, WeierstrassCurve.b₂]
  ring

/-- The actual two gradient values are precisely the coefficients eliminated
by the actual integral translation. -/
theorem translate_critical_iff (W : WeierstrassCurve R) (r t : R) :
    ((translate W r t).a₃ = 0 ∧ (translate W r t).a₄ = 0) ↔
      (W.toAffine.polynomialX.evalEval r t = 0 ∧
        W.toAffine.polynomialY.evalEval r t = 0) := by
  simp only [translate_a3, translate_a4,
    WeierstrassCurve.Affine.evalEval_polynomialX,
    WeierstrassCurve.Affine.evalEval_polynomialY, neg_eq_zero]
  exact and_comm

/-- Translation to the Hensel-lifted critical point gives a₃=a₄=0,
unit b₂, small a₆, and the same actual discriminant. -/
theorem exists_critical_translation_origin [HenselianLocalRing R]
    (W : WeierstrassCurve R) (h3 : W.a₃ ∈ maximalIdeal R)
    (h4 : W.a₄ ∈ maximalIdeal R) (h6 : W.a₆ ∈ maximalIdeal R)
    (hb : IsUnit W.b₂) :
    ∃ r t : R, r ∈ maximalIdeal R ∧ t ∈ maximalIdeal R ∧
      (translate W r t).a₃ = 0 ∧ (translate W r t).a₄ = 0 ∧
      IsUnit (translate W r t).b₂ ∧ (translate W r t).a₆ ∈ maximalIdeal R ∧
      (translate W r t).Δ = W.Δ := by
  obtain ⟨r, t, hr, ht, hx, hy⟩ := exists_critical_origin W h3 h4 hb
  refine ⟨r, t, hr, ht, by simpa only [translate_a3] using hy,
    by simpa only [translate_a4, neg_eq_zero] using hx, ?_, ?_,
    translate_discriminant W r t⟩
  · rw [translate_b2]
    exact IsLocalRing.isUnit_add_of_mem_maximalIdeal _ _ hb ((maximalIdeal R).mul_mem_left _ hr)
  · apply (residue_eq_zero_iff _).mp
    have hrr := (residue_eq_zero_iff _).mpr hr
    have hrt := (residue_eq_zero_iff _).mpr ht
    have hr6 := (residue_eq_zero_iff _).mpr h6
    simp [translate_a6, WeierstrassCurve.Affine.evalEval_polynomial,
      map_sub, map_add, map_mul, map_pow, hrr, hrt, hr6]

@[simp] theorem translate_translate (W : WeierstrassCurve R) (r t x y : R) :
    translate (translate W r t) x y = translate W (r + x) (t + y) := by
  ext <;> simp [translate, WeierstrassCurve.variableChange_def] <;> ring

/-- Hensel-lift an actual residue critical point whose actual Hessian determinant
is nonzero, and translate the same integral Weierstrass equation to that lift.
The result is valid over every henselian local ring, hence over henselian DVRs,
without perfectness or a restriction on residue characteristic. -/
theorem exists_critical_translation [HenselianLocalRing R]
    (W : WeierstrassCurve R) (x y : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation x y)
    (hx : (W.map (residue R)).toAffine.polynomialX.evalEval x y = 0)
    (hy : (W.map (residue R)).toAffine.polynomialY.evalEval x y = 0)
    (hh : criticalHessianDet (W.map (residue R)) x ≠ 0) :
    ∃ r t : R, residue R r = x ∧ residue R t = y ∧
      W.toAffine.polynomialX.evalEval r t = 0 ∧
      W.toAffine.polynomialY.evalEval r t = 0 ∧
      (translate W r t).a₃ = 0 ∧ (translate W r t).a₄ = 0 ∧
      IsUnit (translate W r t).b₂ ∧ (translate W r t).a₆ ∈ maximalIdeal R ∧
      (translate W r t).Δ = W.Δ := by
  obtain ⟨r₀, hr₀⟩ := residue_surjective x
  obtain ⟨t₀, ht₀⟩ := residue_surjective y
  simp only [WeierstrassCurve.Affine.evalEval_polynomialX,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₄] at hx
  simp only [WeierstrassCurve.Affine.evalEval_polynomialY,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at hy
  simp only [WeierstrassCurve.Affine.Equation,
    WeierstrassCurve.Affine.evalEval_polynomial,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆] at he
  have h3 : (translate W r₀ t₀).a₃ ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simpa only [translate_a3, map_add, map_mul, map_ofNat, hr₀, ht₀] using hy
  have h4 : (translate W r₀ t₀).a₄ ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simpa only [translate_a4, map_neg, map_sub, map_add, map_mul, map_pow,
      map_ofNat, hr₀, ht₀, neg_eq_zero] using hx
  have h6 : (translate W r₀ t₀).a₆ ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simpa only [translate_a6, WeierstrassCurve.Affine.evalEval_polynomial,
      map_neg, map_sub, map_add, map_mul, map_pow, map_ofNat, hr₀, ht₀,
      neg_eq_zero] using he
  have hb : IsUnit (translate W r₀ t₀).b₂ := by
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [criticalHessianDet_eq, neg_ne_zero] at hh
    simpa only [translate_b2, map_add, map_mul, map_ofNat, hr₀,
      WeierstrassCurve.map_b₂] using hh
  obtain ⟨r₁, t₁, hr₁, ht₁, h3', h4', hb', h6', hd'⟩ :=
    exists_critical_translation_origin (translate W r₀ t₀) h3 h4 h6 hb
  simp only [translate_translate] at h3' h4' hb' h6'
  obtain ⟨hx', hy'⟩ := (translate_critical_iff W (r₀ + r₁) (t₀ + t₁)).mp ⟨h3', h4'⟩
  refine ⟨r₀ + r₁, t₀ + t₁, ?_, ?_, hx', hy', h3', h4', hb', h6',
    translate_discriminant W _ _⟩
  · simp only [map_add, hr₀, (residue_eq_zero_iff _).mpr hr₁, add_zero]
  · simp only [map_add, ht₀, (residue_eq_zero_iff _).mpr ht₁, add_zero]
end WeierstrassCurve.CriticalPoint

/- Migration source: R5Lab/AlgebraicGeometry/Curves/Nodal/CriticalPoint.lean,
frozen packet f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 20b260971e41f5b97a10a66e9f1cb81b0ca19b5c26fe50866af904cead72162c.
Translation and coefficient maps reuse EllipticCurve.Affine.Coordinates. -/
