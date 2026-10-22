/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.AffineFunctionField
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ProjectiveTranslation
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Normality
public import Aglib.AlgebraicGeometry.Curves.Nodal.CriticalPoint
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Relative smoothness forces nonzero literal Weierstrass discriminant

The actual critical normalization is not surjective on coordinate rings.
Its original fraction-field and integral-closure comparisons show that the
critical ring is not normal. A vanishing discriminant supplies an actual
critical point after internal algebraic closure, in every characteristic.
Literal coefficient base change and translation retain relative smoothness,
which contradicts that nonnormality. No perfectness assumption is made.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial
open scoped Polynomial

universe u

namespace WeierstrassCurve.CriticalCubic

variable (k : Type u) [Field k] (a b : k)

/-- The missing parameter of the actual normalization is not a regular
function on the original critical cubic, in any characteristic. -/
theorem parameter_not_mem_coordinateMap_range :
    (Polynomial.X : k[X]) ∉ Set.range (coordinateMap k a b) := by
  rintro ⟨z, hz⟩
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq z
  have hpq : p.comp (xPolynomial k a b) +
      yPolynomial k a b * q.comp (xPolynomial k a b) = Polynomial.X := by
    simp only [WeierstrassCurve.Affine.CoordinateRing.smul, map_add, map_mul,
      mul_one, coordinateMap_eq_liftAlgHom, WeierstrassCurve.Affine.CoordinateRing.mk,
      AdjoinRoot.liftAlgHom_mk, Polynomial.eval₂_C, Polynomial.eval₂_X] at hz
    simpa only [AlgHom.coe_toRingHom, ← comp_eq_aeval, mul_comm] using hz
  by_cases hq : q = 0
  · simp only [hq, zero_comp, mul_zero, add_zero] at hpq
    have hd := congrArg Polynomial.natDegree hpq
    rw [natDegree_comp, xPolynomial_natDegree, natDegree_X] at hd
    omega
  have hqc : q.comp (xPolynomial k a b) ≠ 0 :=
    mt (comp_x_eq_zero_iff k a b q).mp hq
  have hy : yPolynomial k a b ≠ 0 :=
    mul_ne_zero Polynomial.X_ne_zero (xPolynomial_ne_zero k a b)
  have hpdeg : (p.comp (xPolynomial k a b)).natDegree = 2 * p.natDegree := by
    rw [natDegree_comp, xPolynomial_natDegree, Nat.mul_comm]
  have hqdeg : (yPolynomial k a b * q.comp (xPolynomial k a b)).natDegree =
      3 + 2 * q.natDegree := by
    rw [natDegree_mul hy hqc, yPolynomial_natDegree, natDegree_comp,
      xPolynomial_natDegree, Nat.mul_comm q.natDegree 2]
  have hne : (p.comp (xPolynomial k a b)).natDegree ≠
      (yPolynomial k a b * q.comp (xPolynomial k a b)).natDegree := by
    rw [hpdeg, hqdeg]
    omega
  have hd := congrArg Polynomial.natDegree hpq
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt, hqdeg, natDegree_X] at hd
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt hgt, hpdeg, natDegree_X] at hd
    omega

/-- The actual critical affine cubic is not integrally closed. The proof
uses the native normalization in its original fraction field. -/
theorem coordinateRing_not_isIntegrallyClosed :
    ¬ IsIntegrallyClosed (equation k a b).toAffine.CoordinateRing := by
  intro h
  let A := (equation k a b).toAffine.CoordinateRing
  let K := FractionRing k[X]
  let : IsIntegrallyClosed A := h
  let := (coordinateMap k a b).toRingHom.toAlgebra
  let : IsFractionRing A K := coordinateMap_isFractionRing k a b
  let : IsIntegralClosure k[X] A K := coordinateMap_isIntegralClosure k a b
  let e : A ≃ₐ[A] k[X] := IsIntegralClosure.equiv A A K k[X]
  obtain ⟨z, hz⟩ := e.surjective Polynomial.X
  apply parameter_not_mem_coordinateMap_range k a b
  refine ⟨z, ?_⟩
  have he : e z = coordinateMap k a b z := e.commutes z
  exact he.symm.trans hz

end WeierstrassCurve.CriticalCubic

namespace WeierstrassCurve

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem cubic_repeated_coefficients (P : Cubic k) (ha : P.a ≠ 0)
    (hΔ : P.discr = 0) :
    ∃ r t : k, P.b = P.a * -(r + r + t) ∧
      P.c = P.a * (r * r + r * t + r * t) ∧ P.d = P.a * -(r * r * t) := by
  obtain ⟨r, s, t, hroots⟩ :=
    (Cubic.splits_iff_roots_eq_three (φ := RingHom.id k) ha).mp (IsAlgClosed.splits _)
  have hb := Cubic.b_eq_three_roots ha hroots
  have hc := Cubic.c_eq_three_roots ha hroots
  have hd := Cubic.d_eq_three_roots ha hroots
  simp only [RingHom.id_apply] at hb hc hd
  have hnot : ¬ (r ≠ s ∧ r ≠ t ∧ s ≠ t) := by
    intro h
    exact ((Cubic.discr_ne_zero_iff_roots_ne ha hroots).mpr h) hΔ
  have heq : r = s ∨ r = t ∨ s = t := by tauto
  rcases heq with h | h | h
  · subst s
    refine ⟨r, t, ?_, ?_, ?_⟩
    · linear_combination hb
    · linear_combination hc
    · linear_combination hd
  · subst t
    refine ⟨r, s, ?_, ?_, ?_⟩
    · linear_combination hb
    · linear_combination hc
    · linear_combination hd
  · subst t
    refine ⟨s, r, ?_, ?_, ?_⟩
    · linear_combination hb
    · linear_combination hc
    · linear_combination hd

/-- Over an algebraic closure, vanishing literal discriminant produces an
actual affine point and both actual gradient equations in all characteristics. -/
theorem exists_critical_point_of_discriminant_eq_zero
    (W : WeierstrassCurve k) (hΔ : W.Δ = 0) :
    ∃ r t : k, W.toAffine.Equation r t ∧
      W.toAffine.polynomialX.evalEval r t = 0 ∧ W.toAffine.polynomialY.evalEval r t = 0 := by
  by_cases h2 : (2 : k) = 0
  · have h4 : (4 : k) = 0 := by linear_combination 2 * h2
    have h8 : (8 : k) = 0 := by linear_combination 4 * h2
    have h27 : (27 : k) = 1 := by linear_combination 13 * h2
    have h432 : (432 : k) = 0 := by linear_combination 216 * h2
    by_cases h1 : W.a₁ = 0
    · have h3 : W.a₃ = 0 := by
        simpa [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, h1, h2, h4, h8, h27] using hΔ
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (-W.a₄) (n := 2) (by decide)
      obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq
        (r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆) (n := 2) (by decide)
      have hthree : (3 : k) = 1 := by linear_combination h2
      refine ⟨r, t, ?_, ?_, ?_⟩
      · rw [Affine.Equation, Affine.evalEval_polynomial, h1, h3, ht]
        ring
      · rw [Affine.evalEval_polynomialX, h1, h2, hthree, hr]
        ring
      · simp [Affine.evalEval_polynomialY, h1, h2, h3]
    · let r := -W.a₃ / W.a₁
      let t := (3 * r ^ 2 + 2 * W.a₂ * r + W.a₄) / W.a₁
      have hy : 2 * t + W.a₁ * r + W.a₃ = 0 := by
        rw [h2, zero_mul, zero_add]
        dsimp only [r]
        field_simp [h1]; ring
      have hx : W.a₁ * t - (3 * r ^ 2 + 2 * W.a₂ * r + W.a₄) = 0 := by
        dsimp only [t]
        field_simp [h1]
        ring
      have ht3 : (translate W r t).a₃ = 0 := (translate_a3 W r t).trans hy
      have ht4 : (translate W r t).a₄ = 0 := by rw [translate_a4, hx, neg_zero]
      have hb : (translate W r t).b₂ = W.a₁ ^ 2 := by
        simp only [b₂, translate_a1, h4, zero_mul, add_zero]
      have hdc : (translate W r t).Δ = 0 := by rw [translate_discriminant, hΔ]
      rw [CriticalPoint.discriminant_critical_factor _ ht3 ht4, hb,
        h432, zero_mul, add_zero] at hdc
      have ht6 : (translate W r t).a₆ = 0 :=
        (mul_eq_zero.mp hdc).resolve_right (neg_ne_zero.mpr (pow_ne_zero 3 (pow_ne_zero 2 h1)))
      refine ⟨r, t, ?_, ?_, ?_⟩
      · rw [Affine.Equation]
        exact neg_eq_zero.mp ((translate_a6 W r t).symm.trans ht6)
      · exact (Affine.evalEval_polynomialX (W := W.toAffine) r t).trans hx
      · exact (Affine.evalEval_polynomialY (W := W.toAffine) r t).trans hy
  · have h4 : (4 : k) ≠ 0 := by
      simpa only [show (4 : k) = 2 ^ 2 by norm_num] using pow_ne_zero 2 h2
    have hD : W.twoTorsionPolynomial.discr = 0 := by rw [twoTorsionPolynomial_discr, hΔ, mul_zero]
    obtain ⟨r, s, hb, hc, hd⟩ := cubic_repeated_coefficients W.twoTorsionPolynomial h4 hD
    change W.b₂ = 4 * -(r + r + s) at hb
    change 2 * W.b₄ = 4 * (r * r + r * s + r * s) at hc
    change W.b₆ = 4 * -(r * r * s) at hd
    have hcrit : 6 * r ^ 2 + W.b₂ * r + W.b₄ = 0 := by
      have H : 2 * (6 * r ^ 2 + W.b₂ * r + W.b₄) = 0 := by
        linear_combination 2 * r * hb + hc
      exact (mul_eq_zero.mp H).resolve_left h2
    have hroot : 4 * r ^ 3 + W.b₂ * r ^ 2 + 2 * W.b₄ * r + W.b₆ = 0 := by
      linear_combination r ^ 2 * hb + r * hc + hd
    let t := -(W.a₁ * r + W.a₃) / 2
    have hy : 2 * t + W.a₁ * r + W.a₃ = 0 := by
      dsimp only [t]
      field_simp [h2]; ring
    have hx : W.a₁ * t - (3 * r ^ 2 + 2 * W.a₂ * r + W.a₄) = 0 := by
      have H : 2 * (W.a₁ * t - (3 * r ^ 2 + 2 * W.a₂ * r + W.a₄)) = 0 := by
        dsimp only [b₂, b₄] at hcrit
        linear_combination W.a₁ * hy - hcrit
      exact (mul_eq_zero.mp H).resolve_left h2
    refine ⟨r, t, ?_, ?_, ?_⟩
    · rw [Affine.Equation]
      have H : 4 * W.toAffine.polynomial.evalEval r t = 0 := by
        rw [Affine.evalEval_polynomial]
        dsimp only [b₂, b₄, b₆] at hroot
        linear_combination (2 * t + W.a₁ * r + W.a₃) * hy - hroot
      exact (mul_eq_zero.mp H).resolve_left h4
    · exact (Affine.evalEval_polynomialX (W := W.toAffine) r t).trans hx
    · exact (Affine.evalEval_polynomialY (W := W.toAffine) r t).trans hy

end WeierstrassCurve

namespace WeierstrassCurve.Projective

variable {k : Type u} [Field k]

/-- Actual relative smoothness of the literal projective Weierstrass cubic
forces its literal discriminant to be nonzero over every field. Algebraic
closure is used only as an internal faithful coefficient base change. -/
theorem discriminant_ne_zero_of_smooth (W : WeierstrassCurve k)
    (hW : Smooth (structureMap W)) : W.Δ ≠ 0 := by
  intro hΔ
  let K := AlgebraicClosure k
  let V := W.baseChange K
  let : Smooth (structureMap W) := hW
  let eB := coefficientBaseChangeIso (S := K) W
  have hbase : eB.hom ≫
      Limits.pullback.snd (structureMap W) (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      structureMap V := coefficientBaseChangeIso_hom_snd W
  let : Smooth (structureMap V) := by
    rw [← hbase]
    infer_instance
  have hΔV : V.Δ = 0 := by
    simp only [V, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, hΔ, map_zero]
  obtain ⟨r, t, he, hx, hy⟩ := exists_critical_point_of_discriminant_eq_zero V hΔV
  let E := Translation.originalToCriticalOverIso V r t he hx hy
  let C := CriticalCubic.equation K V.a₁ (V.a₂ + 3 * r)
  let : IsIso E.inv.left := inferInstanceAs (IsIso ((Over.forget _).map E.inv))
  have hE : E.inv.left ≫ structureMap V = structureMap C := E.inv.w
  let : Smooth (structureMap C) := by
    rw [← hE]
    infer_instance
  have hA : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (affineRing C)))) := by
    rw [← affineChart_structure C]
    infer_instance
  have hnormal := coordinateRing_integrallyClosed_of_smoothSpec K (affineRing C) hA
  exact CriticalCubic.coordinateRing_not_isIntegrallyClosed K V.a₁ (V.a₂ + 3 * r) hnormal

end WeierstrassCurve.Projective
