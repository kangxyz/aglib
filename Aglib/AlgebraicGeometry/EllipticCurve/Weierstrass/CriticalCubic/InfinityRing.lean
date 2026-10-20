/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.AffinePinching
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineChart

/-!
# An adapted infinity ring of the critical cubic

The literal homogeneous chart away from Y−rX is identified with the
localized polynomial infinity chart. Both ring maps and inverse formulas
are constructed from the homogeneous quotient and the exact two-root equations.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial
universe u

namespace WeierstrassCurve.CriticalCubic.AdaptedInfinity

open WeierstrassCurve.Projective
variable (k : Type u) [Field k] (a b r : k)
local notation "W" => CriticalCubic.equation k a b
local notation "H" => homogeneousCoordinateRing W

/-- The actual homogeneous linear form, in the original cubic coordinate ring. -/
def denominator : H := coordinate W 1 - algebraMap k H r * coordinate W 0

lemma denominator_mem : denominator k a b r ∈ grading W 1 := by
  apply Submodule.mem_map.mpr
  refine ⟨MvPolynomial.X 1 - MvPolynomial.C r * MvPolynomial.X 0,
    (MvPolynomial.isHomogeneous_X k 1).sub (MvPolynomial.isHomogeneous_C_mul_X r 0), ?_⟩
  change Ideal.Quotient.mk (cubicIdeal W)
    (MvPolynomial.X 1 - MvPolynomial.C r * MvPolynomial.X 0) = denominator k a b r
  simp only [map_sub, map_mul, denominator, coordinate]
  rfl

/-- The degree-zero homogeneous chart ring away from `Y - rX`. -/
abbrev ChartRing := HomogeneousLocalization.Away (grading W) (denominator k a b r)
/-- The ordinary localization of the homogeneous coordinate ring away from `Y - rX`. -/
abbrev OrdinaryRing := Localization.Away (denominator k a b r)

/-- The original field's actual scalar map into this homogeneous localization. -/
def scalar : k →+* ChartRing k a b r :=
  (HomogeneousLocalization.fromZeroRingHom (grading W)
    (Submonoid.powers (denominator k a b r))).comp (constToGradeZero W)

/-- The original homogeneous coordinate divided by the actual L. -/
def normalizedCoordinate (i : Fin 3) : ChartRing k a b r :=
  HomogeneousLocalization.Away.mk (grading W) (denominator_mem k a b r) 1
    (coordinate W i) (by simpa using coordinate_mem W i)

/-- The inverse of `Y - rX` in its ordinary localization. -/
def denominatorInverse : OrdinaryRing k a b r :=
  IsLocalization.Away.invSelf (denominator k a b r)

lemma scalar_val (c : k) :
    (scalar k a b r c).val = algebraMap H (OrdinaryRing k a b r) (algebraMap k H c) := by
  simp only [scalar, RingHom.comp_apply, HomogeneousLocalization.fromZeroRingHom,
    constToGradeZero]
  change Localization.mk _ 1 = _
  exact Localization.mk_one_eq_algebraMap _

lemma normalizedCoordinate_val (i : Fin 3) :
    (normalizedCoordinate k a b r i).val = denominatorInverse k a b r *
      algebraMap H (OrdinaryRing k a b r) (coordinate W i) := by
  simp only [normalizedCoordinate, HomogeneousLocalization.Away.val_mk, pow_one,
    denominatorInverse, IsLocalization.Away.invSelf, Localization.mk_eq_mk']
  rw [mul_comm, IsLocalization.mk'_eq_mul_mk'_one]

lemma normalized_linear_relation :
    normalizedCoordinate k a b r 1 - scalar k a b r r * normalizedCoordinate k a b r 0 = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_sub, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_one, normalizedCoordinate_val, scalar_val]
  have h := IsLocalization.Away.mul_invSelf
    (S := OrdinaryRing k a b r) (denominator k a b r)
  change algebraMap H (OrdinaryRing k a b r) (denominator k a b r) *
    denominatorInverse k a b r = 1 at h
  simp only [denominator, map_sub, map_mul] at h
  linear_combination h

/-- Literal polynomial evaluation at X/L, Y/L, Z/L. -/
def normalizePolynomial : MvPolynomial (Fin 3) k →+* ChartRing k a b r :=
  MvPolynomial.eval₂Hom (scalar k a b r) (normalizedCoordinate k a b r)

lemma normalizePolynomial_val (p : MvPolynomial (Fin 3) k) {n : ℕ}
    (hp : p.IsHomogeneous n) :
    (normalizePolynomial k a b r p).val = denominatorInverse k a b r ^ n *
      algebraMap H (OrdinaryRing k a b r) (Ideal.Quotient.mk (cubicIdeal W) p) := by
  change (algebraMap (ChartRing k a b r) (OrdinaryRing k a b r)).comp
    (normalizePolynomial k a b r) p = _
  rw [normalizePolynomial, MvPolynomial.comp_eval₂Hom]
  simp only [HomogeneousLocalization.algebraMap_apply, normalizedCoordinate_val]
  rw [homogeneous_eval_scale p hp]
  congr 1
  have h : MvPolynomial.eval₂Hom
      ((algebraMap (ChartRing k a b r) (OrdinaryRing k a b r)).comp (scalar k a b r))
      (fun i => algebraMap H (OrdinaryRing k a b r) (coordinate W i)) =
      (algebraMap H (OrdinaryRing k a b r)).comp (Ideal.Quotient.mk (cubicIdeal W)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have hc : algebraMap k H c = Ideal.Quotient.mk (cubicIdeal W) (MvPolynomial.C c) := rfl
      simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C,
        HomogeneousLocalization.algebraMap_apply, hc] using scalar_val k a b r c
    · intro i
      simp [coordinate]
  exact congrArg (fun f : MvPolynomial (Fin 3) k →+* OrdinaryRing k a b r => f p) h

lemma normalizePolynomial_homogeneous (p : MvPolynomial (Fin 3) k) {n : ℕ}
    (hp : p.IsHomogeneous n) :
    normalizePolynomial k a b r p = HomogeneousLocalization.Away.mk (grading W)
      (denominator_mem k a b r) n (Ideal.Quotient.mk (cubicIdeal W) p)
      (by
        simp only [smul_eq_mul, mul_one]
        exact Submodule.mem_map.mpr ⟨p, hp, rfl⟩) := by
  apply HomogeneousLocalization.val_injective
  rw [normalizePolynomial_val k a b r p hp, HomogeneousLocalization.Away.val_mk]
  simp only [denominatorInverse, IsLocalization.Away.invSelf,
    Localization.mk_eq_mk', ← IsLocalization.mk'_pow, one_pow]
  rw [mul_comm]
  conv_rhs => rw [IsLocalization.mk'_eq_mul_mk'_one]
  rfl

lemma normalized_cubic_relation : normalizePolynomial k a b r
  (WeierstrassCurve.Projective.polynomial
      (WeierstrassCurve.toProjective (CriticalCubic.equation k a b))) = 0 := by
  apply HomogeneousLocalization.val_injective
  have hz : Ideal.Quotient.mk (cubicIdeal W) (WeierstrassCurve.Projective.polynomial
      (WeierstrassCurve.toProjective (CriticalCubic.equation k a b))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [normalizePolynomial_val k a b r _ (cubic_homogeneous W), hz,
    map_zero, mul_zero, HomogeneousLocalization.val_zero]

/-- The adapted reciprocal parameter, on the actual homogeneous chart. -/
def parameter (s : k) : ChartRing k a b r :=
  scalar k a b r (s - r) * normalizedCoordinate k a b r 0

lemma parameter_relation (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    (1 - parameter k a b r s) * scalar k a b r (s - r) ^ 3 *
      normalizedCoordinate k a b r 2 = parameter k a b r s ^ 3 := by
  have hc := normalized_cubic_relation k a b r
  simp only [normalizePolynomial, WeierstrassCurve.Projective.polynomial,
    CriticalCubic.equation, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
    map_zero, zero_mul, add_zero] at hc
  obtain ⟨ha, hb⟩ := CriticalCubic.coefficients_of_two_roots k a b r s hrs hr hs
  have ha' := congrArg (scalar k a b r) ha
  have hb' := congrArg (scalar k a b r) hb
  simp only [map_neg, map_add, map_mul] at ha' hb'
  rw [ha', hb'] at hc
  have hf : (normalizedCoordinate k a b r 1 - scalar k a b r r * normalizedCoordinate k a b r 0) *
      (normalizedCoordinate k a b r 1 - scalar k a b r s * normalizedCoordinate k a b r 0) *
        normalizedCoordinate k a b r 2 = normalizedCoordinate k a b r 0 ^ 3 := by
    linear_combination hc
  have hy : normalizedCoordinate k a b r 1 - scalar k a b r s * normalizedCoordinate k a b r 0 =
      1 - scalar k a b r (s - r) * normalizedCoordinate k a b r 0 := by
    rw [map_sub]
    linear_combination normalized_linear_relation k a b r
  rw [normalized_linear_relation k a b r, one_mul, hy] at hf
  dsimp [parameter]
  calc
    (1 - scalar k a b r (s - r) * normalizedCoordinate k a b r 0) *
        scalar k a b r (s - r) ^ 3 * normalizedCoordinate k a b r 2 =
      scalar k a b r (s - r) ^ 3 *
        ((1 - scalar k a b r (s - r) * normalizedCoordinate k a b r 0) *
          normalizedCoordinate k a b r 2) := by ring
    _ = scalar k a b r (s - r) ^ 3 * normalizedCoordinate k a b r 0 ^ 3 := by rw [hf]
    _ = (scalar k a b r (s - r) * normalizedCoordinate k a b r 0) ^ 3 := by ring

lemma parameter_sub_one_isUnit (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    IsUnit (parameter k a b r s - 1) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨-(1 + parameter k a b r s + parameter k a b r s ^ 2 +
    scalar k a b r (s - r) ^ 3 * normalizedCoordinate k a b r 2), ?_⟩
  linear_combination parameter_relation k a b r s hrs hr hs

local notation "V" => Polynomial.PinchedPair.infinityChartRing k

/-- The permanent infinity-chart parameter and its existing localization inverse. -/
def standardParameter : V := algebraMap k[X] V Polynomial.X
/-- The inverse of `X - 1` in the standard infinity chart ring. -/
def standardInverse : V := IsLocalization.Away.invSelf (Polynomial.X - 1 : k[X])

lemma standard_inverse_relation : (standardParameter k - 1) * standardInverse k = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := V) (Polynomial.X - 1 : k[X])
  change algebraMap k[X] V (Polynomial.X - 1) * standardInverse k = 1 at h
  rw [(algebraMap k[X] V).map_sub, (algebraMap k[X] V).map_one] at h
  exact h

/-- The actual inverse-chart coordinate formulas, over the original field. -/
def xValue (s : k) : V := algebraMap k V (s - r)⁻¹ * standardParameter k
/-- The image of the normalized homogeneous `Y` coordinate, expressed as `1 + r * xValue`. -/
def yValue (s : k) : V := 1 + algebraMap k V r * xValue k r s
/-- The image of the normalized homogeneous `Z` coordinate in the standard infinity chart ring. -/
def zValue (s : k) : V :=
  -(algebraMap k V (s - r)⁻¹) ^ 3 * standardParameter k ^ 3 * standardInverse k

lemma value_left_linear (s : k) :
    yValue k r s - algebraMap k V r * xValue k r s = 1 := by
  dsimp [yValue]
  ring

lemma value_right_linear (s : k) (hrs : r ≠ s) :
    yValue k r s - algebraMap k V s * xValue k r s = 1 - standardParameter k := by
  have hd : s - r ≠ 0 := sub_ne_zero.mpr hrs.symm
  have hδ : algebraMap k V (s - r) * algebraMap k V (s - r)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  calc
    yValue k r s - algebraMap k V s * xValue k r s =
        1 - algebraMap k V (s - r) * (algebraMap k V (s - r)⁻¹ * standardParameter k) := by
      simp only [yValue, xValue, map_sub]
      ring
    _ = 1 - standardParameter k := by rw [← mul_assoc, hδ, one_mul]

lemma values_factor_relation (s : k) (hrs : r ≠ s) :
    (yValue k r s - algebraMap k V r * xValue k r s) *
      (yValue k r s - algebraMap k V s * xValue k r s) * zValue k r s - xValue k r s ^ 3 = 0 := by
  rw [value_left_linear, one_mul, value_right_linear k r s hrs]
  dsimp [zValue, xValue]
  calc
    (1 - standardParameter k) *
        (-(algebraMap k V (s - r)⁻¹) ^ 3 * standardParameter k ^ 3 * standardInverse k) -
          (algebraMap k V (s - r)⁻¹ * standardParameter k) ^ 3 =
      (algebraMap k V (s - r)⁻¹) ^ 3 * standardParameter k ^ 3 *
        ((standardParameter k - 1) * standardInverse k - 1) := by ring
    _ = 0 := by rw [standard_inverse_relation]; ring

lemma values_cubic_relation (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    yValue k r s ^ 2 * zValue k r s + algebraMap k V a * xValue k r s * yValue k r s * zValue k r
      s -
      (xValue k r s ^ 3 + algebraMap k V b * xValue k r s ^ 2 * zValue k r s) = 0 := by
  obtain ⟨ha, hb⟩ := CriticalCubic.coefficients_of_two_roots k a b r s hrs hr hs
  rw [ha, hb]
  simp only [map_neg, map_add, map_mul]
  linear_combination values_factor_relation k r s hrs

/-- Evaluation of the original homogeneous quotient at the explicit L=1 coordinates. -/
def dehomogenize (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) : H →+* V :=
  Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (algebraMap k V) ![xValue k r s, yValue k r s, zValue k r s]) (by
      change cubicIdeal W ≤ RingHom.ker _
      apply Ideal.span_le.mpr
      intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      change MvPolynomial.eval₂Hom (algebraMap k V)
        ![xValue k r s, yValue k r s, zValue k r s] (WeierstrassCurve.Projective.polynomial
      (WeierstrassCurve.toProjective (CriticalCubic.equation k a b))) = 0
      simpa only [WeierstrassCurve.Projective.polynomial, CriticalCubic.equation,
        WeierstrassCurve.toProjective, map_add, map_sub, map_mul, map_pow,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, map_zero, zero_mul, add_zero] using
          values_cubic_relation k a b r s hrs hr hs)

@[simp] lemma dehomogenize_coordinate (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (i : Fin 3) :
    dehomogenize k a b r s hrs hr hs (coordinate W i) =
      ![xValue k r s, yValue k r s, zValue k r s] i := by
  simp [dehomogenize, coordinate]

@[simp] lemma dehomogenize_scalar (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (c : k) :
    dehomogenize k a b r s hrs hr hs (algebraMap k H c) = algebraMap k V c := by
  change dehomogenize k a b r s hrs hr hs (Ideal.Quotient.mk _ (MvPolynomial.C c)) = _
  simp [dehomogenize]

@[simp] lemma dehomogenize_denominator (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    dehomogenize k a b r s hrs hr hs (denominator k a b r) = 1 := by
  simpa only [denominator, map_sub, map_mul, dehomogenize_coordinate, dehomogenize_scalar,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using value_left_linear k r s

/-- The chart-to-standard map uses the actual homogeneous localization inclusion. -/
def fromChart (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) : ChartRing k a b r →+* V :=
  (Localization.awayLift (dehomogenize k a b r s hrs hr hs) (denominator k a b r) (by simp)).comp
    (algebraMap (ChartRing k a b r) (OrdinaryRing k a b r))

lemma fromChart_mk (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0)
    (n : ℕ) (z : H) (hz : z ∈ grading W (n • 1)) :
    fromChart k a b r s hrs hr hs
      (HomogeneousLocalization.Away.mk (grading W) (denominator_mem k a b r) n z hz) =
        dehomogenize k a b r s hrs hr hs z := by
  simpa only [fromChart, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, dehomogenize_denominator, one_pow, mul_one] using
    Localization.awayLift_mk (dehomogenize k a b r s hrs hr hs)
      (denominator k a b r) z 1 (by simp) n

@[simp] lemma fromChart_coordinate (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (i : Fin 3) :
    fromChart k a b r s hrs hr hs (normalizedCoordinate k a b r i) =
      ![xValue k r s, yValue k r s, zValue k r s] i := by
  rw [normalizedCoordinate, fromChart_mk, dehomogenize_coordinate]

@[simp] lemma fromChart_scalar (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (c : k) :
    fromChart k a b r s hrs hr hs (scalar k a b r c) = algebraMap k V c := by
  change Localization.awayLift (dehomogenize k a b r s hrs hr hs) (denominator k a b r)
    (by simp) (scalar k a b r c).val = _
  rw [scalar_val, IsLocalization.Away.lift_eq, dehomogenize_scalar]

@[simp] lemma fromChart_parameter (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    fromChart k a b r s hrs hr hs (parameter k a b r s) = standardParameter k := by
  rw [parameter, map_mul, fromChart_scalar, fromChart_coordinate]
  simp only [Matrix.cons_val_zero, xValue]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (sub_ne_zero.mpr hrs.symm), map_one, one_mul]

/-- The reverse ring map sends the permanent infinity variable to δX/(Y-rX). -/
def toChart (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) : V →+* ChartRing k a b r :=
  IsLocalization.Away.lift (Polynomial.X - 1 : k[X])
    (g := Polynomial.eval₂RingHom (scalar k a b r) (parameter k a b r s)) (by
      simpa only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_one] using parameter_sub_one_isUnit k a b r s hrs hr hs)

@[simp] lemma toChart_polynomial (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (p : k[X]) :
    toChart k a b r s hrs hr hs (algebraMap k[X] V p) =
      Polynomial.eval₂ (scalar k a b r) (parameter k a b r s) p :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] lemma toChart_scalar (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (c : k) :
    toChart k a b r s hrs hr hs (algebraMap k V c) = scalar k a b r c := by
  change toChart k a b r s hrs hr hs (algebraMap k[X] V (Polynomial.C c)) = _
  rw [toChart_polynomial, Polynomial.eval₂_C]

@[simp] lemma toChart_parameter (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    toChart k a b r s hrs hr hs (standardParameter k) = parameter k a b r s := by
  rw [standardParameter, toChart_polynomial, Polynomial.eval₂_X]

@[simp] lemma toChart_xValue (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    toChart k a b r s hrs hr hs (xValue k r s) = normalizedCoordinate k a b r 0 := by
  rw [xValue, map_mul, toChart_scalar, toChart_parameter, parameter]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hrs.symm), map_one, one_mul]

@[simp] lemma toChart_yValue (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    toChart k a b r s hrs hr hs (yValue k r s) = normalizedCoordinate k a b r 1 := by
  simp only [yValue, map_add, map_one, map_mul, toChart_scalar, toChart_xValue]
  linear_combination -(normalized_linear_relation k a b r)

@[simp] lemma toChart_zValue (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    toChart k a b r s hrs hr hs (zValue k r s) = normalizedCoordinate k a b r 2 := by
  have hj := congrArg (toChart k a b r s hrs hr hs) (standard_inverse_relation k)
  simp only [map_mul, map_sub, map_one, toChart_parameter] at hj
  have hδ : scalar k a b r (s - r)⁻¹ * scalar k a b r (s - r) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hrs.symm), map_one]
  simp only [zValue, map_neg, map_pow, map_mul, toChart_scalar, toChart_parameter]
  rw [← parameter_relation k a b r s hrs hr hs]
  calc
    -(scalar k a b r (s - r)⁻¹) ^ 3 *
        ((1 - parameter k a b r s) * scalar k a b r (s - r) ^ 3 * normalizedCoordinate k a b r 2) *
          toChart k a b r s hrs hr hs (standardInverse k) =
      (scalar k a b r (s - r)⁻¹ * scalar k a b r (s - r)) ^ 3 *
        ((parameter k a b r s - 1) * toChart k a b r s hrs hr hs (standardInverse k)) *
          normalizedCoordinate k a b r 2 := by ring
    _ = normalizedCoordinate k a b r 2 := by rw [hδ, hj]; ring

lemma toChart_dehomogenize (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0)
    (p : MvPolynomial (Fin 3) k) :
    toChart k a b r s hrs hr hs
      (dehomogenize k a b r s hrs hr hs (Ideal.Quotient.mk (cubicIdeal W) p)) =
        normalizePolynomial k a b r p := by
  have h : (toChart k a b r s hrs hr hs).comp
      (MvPolynomial.eval₂Hom (algebraMap k V) ![xValue k r s, yValue k r s, zValue k r s]) =
      normalizePolynomial k a b r := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [normalizePolynomial]
    · intro i
      fin_cases i <;> simp [normalizePolynomial]
  exact congrArg (fun f : MvPolynomial (Fin 3) k →+* ChartRing k a b r => f p) h

lemma to_fromChart (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (z : ChartRing k a b r) :
    toChart k a b r s hrs hr hs (fromChart k a b r s hrs hr hs z) = z := by
  obtain ⟨n, q, hq, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading W) (denominator_mem k a b r) z
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
  rw [fromChart_mk]
  change toChart k a b r s hrs hr hs
    (dehomogenize k a b r s hrs hr hs (Ideal.Quotient.mk (cubicIdeal W) p)) = _
  rw [toChart_dehomogenize]
  exact normalizePolynomial_homogeneous k a b r p (by simpa using hp)

lemma from_toChart (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (z : V) :
    fromChart k a b r s hrs hr hs (toChart k a b r s hrs hr hs z) = z := by
  have h : (fromChart k a b r s hrs hr hs).comp (toChart k a b r s hrs hr hs) = RingHom.id V := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X - 1 : k[X]))
    apply Polynomial.ringHom_ext
    · intro c
      change fromChart k a b r s hrs hr hs
        (toChart k a b r s hrs hr hs (algebraMap k V c)) = algebraMap k V c
      rw [toChart_scalar, fromChart_scalar]
    · change fromChart k a b r s hrs hr hs
        (toChart k a b r s hrs hr hs (standardParameter k)) = standardParameter k
      rw [toChart_parameter, fromChart_parameter]
  exact congrArg (fun f : V →+* V => f z) h

/-- Actual two-sided inverse of the literal adapted homogeneous chart ring. -/
def ringEquiv (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    V ≃+* ChartRing k a b r where
  __ := toChart k a b r s hrs hr hs
  invFun := fromChart k a b r s hrs hr hs
  left_inv := from_toChart k a b r s hrs hr hs
  right_inv := to_fromChart k a b r s hrs hr hs

@[simp] lemma ringEquiv_scalar (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) (c : k) :
    ringEquiv k a b r s hrs hr hs (algebraMap k V c) = scalar k a b r c :=
  toChart_scalar k a b r s hrs hr hs c

@[simp] lemma ringEquiv_parameter (s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0) :
    ringEquiv k a b r s hrs hr hs (standardParameter k) =
      scalar k a b r (s - r) * normalizedCoordinate k a b r 0 :=
  toChart_parameter k a b r s hrs hr hs
end WeierstrassCurve.CriticalCubic.AdaptedInfinity

/- Migration source: LocalModels/CriticalCubic/InfinityRing.lean.
Frozen R5 packet f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 1f3b0d1e1ddfeacbaa850c130de00c067bb56b713ef79aa8e1fd32afbf66b245. -/
