/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Projective
public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.Coordinates
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# The affine chart of the projective Weierstrass cubic

Source: ordinary R5 Weierstrass.Projective, lines 436–715.
The affine ring is Mathlib Affine.CoordinateRing. Both chart ring arrows
and their inverse identities are proved on the actual coordinates.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped BigOperators
namespace WeierstrassCurve.Projective
universe u
variable {k : Type u} [CommRing k]

lemma homogeneous_eval_scale {σ S : Type*} [CommRing S] (p : MvPolynomial σ k)
    {n : ℕ} (hp : p.IsHomogeneous n) (f : k →+* S) (v : σ → S) (c : S) :
    eval₂Hom f (fun i => c * v i) p = c ^ n * eval₂Hom f v p := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff]
  conv_rhs => rw [← p.support_sum_monomial_coeff]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [eval₂Hom_monomial, mul_pow, Finsupp.prod_mul]
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← hp.degree_eq_sum_deg_support hd]
  ring

/-- The homomorphism embedding base-ring constants into a standard chart ring. -/
def chartConstant (W : WeierstrassCurve k) (i : Fin 3) : k →+* chartRing W i :=
  (HomogeneousLocalization.fromZeroRingHom (grading W)
    (Submonoid.powers (coordinate W i))).comp (constToGradeZero W)

/-- The chart coordinate given by the ratio of coordinate `j` to coordinate `i`. -/
def normalizedCoordinate (W : WeierstrassCurve k) (i j : Fin 3) : chartRing W i :=
  HomogeneousLocalization.Away.mk (grading W) (coordinate_mem W i) 1
    (coordinate W j) (by simpa using coordinate_mem W j)

/-- The ordinary localization of the homogeneous coordinate ring at coordinate `i`. -/
abbrev ordinaryChartRing (W : WeierstrassCurve k) (i : Fin 3) :=
  Localization.Away (coordinate W i)
/-- The inverse of coordinate `i` in the ordinary localization at that coordinate. -/
def denominatorInverse (W : WeierstrassCurve k) (i : Fin 3) : ordinaryChartRing W i :=
  IsLocalization.Away.invSelf (coordinate W i)

lemma chartConstant_val (W : WeierstrassCurve k) (i : Fin 3) (a : k) :
    (chartConstant W i a).val = algebraMap _ (ordinaryChartRing W i)
      (algebraMap k (homogeneousCoordinateRing W) a) := by
  simp only [chartConstant, RingHom.comp_apply, HomogeneousLocalization.fromZeroRingHom,
    constToGradeZero]
  change Localization.mk _ 1 = _
  exact Localization.mk_one_eq_algebraMap _

lemma normalizedCoordinate_val (W : WeierstrassCurve k) (i j : Fin 3) :
    (normalizedCoordinate W i j).val = denominatorInverse W i *
      algebraMap _ (ordinaryChartRing W i) (coordinate W j) := by
  simp only [normalizedCoordinate, HomogeneousLocalization.Away.val_mk, pow_one,
    denominatorInverse, IsLocalization.Away.invSelf, Localization.mk_eq_mk']
  rw [mul_comm, IsLocalization.mk'_eq_mul_mk'_one]

@[simp] lemma normalizedCoordinate_self (W : WeierstrassCurve k) (i : Fin 3) :
    normalizedCoordinate W i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [normalizedCoordinate_val, HomogeneousLocalization.val_one, mul_comm]
  exact IsLocalization.Away.mul_invSelf _

/-- Evaluate a homogeneous-coordinate polynomial at the normalized chart coordinates. -/
def normalizePolynomial (W : WeierstrassCurve k) (i : Fin 3) :
    MvPolynomial (Fin 3) k →+* chartRing W i :=
  eval₂Hom (chartConstant W i) (normalizedCoordinate W i)

lemma normalizePolynomial_val (W : WeierstrassCurve k) (i : Fin 3)
    (p : MvPolynomial (Fin 3) k) {n : ℕ} (hp : p.IsHomogeneous n) :
    (normalizePolynomial W i p).val = denominatorInverse W i ^ n *
      algebraMap _ (ordinaryChartRing W i) (Ideal.Quotient.mk (cubicIdeal W) p) := by
  change (algebraMap (chartRing W i) (ordinaryChartRing W i)).comp
    (normalizePolynomial W i) p = _
  rw [normalizePolynomial, MvPolynomial.comp_eval₂Hom]
  simp only [HomogeneousLocalization.algebraMap_apply, normalizedCoordinate_val]
  rw [homogeneous_eval_scale p hp]
  congr 1
  have h : eval₂Hom ((algebraMap (chartRing W i) (ordinaryChartRing W i)).comp
      (chartConstant W i)) (fun j => algebraMap _ (ordinaryChartRing W i) (coordinate W j)) =
      (algebraMap _ (ordinaryChartRing W i)).comp (Ideal.Quotient.mk (cubicIdeal W)) := by
    ext a
    · have hc : algebraMap k (homogeneousCoordinateRing W) a =
          Ideal.Quotient.mk (cubicIdeal W) (C a) := rfl
      simpa only [RingHom.comp_apply, eval₂Hom_C, HomogeneousLocalization.algebraMap_apply, hc]
        using chartConstant_val W i a
    · simp [coordinate]
  exact congrArg (fun f : MvPolynomial (Fin 3) k →+* ordinaryChartRing W i => f p) h

lemma normalizePolynomial_homogeneous (W : WeierstrassCurve k) (i : Fin 3)
    (p : MvPolynomial (Fin 3) k) {n : ℕ} (hp : p.IsHomogeneous n) :
    normalizePolynomial W i p = HomogeneousLocalization.Away.mk (grading W)
      (coordinate_mem W i) n (Ideal.Quotient.mk (cubicIdeal W) p)
      (by
        simp only [smul_eq_mul, mul_one]
        exact Submodule.mem_map.mpr ⟨p, hp, rfl⟩) := by
  apply HomogeneousLocalization.val_injective
  rw [normalizePolynomial_val W i p hp, HomogeneousLocalization.Away.val_mk]
  simp only [denominatorInverse, IsLocalization.Away.invSelf,
    Localization.mk_eq_mk', ← IsLocalization.mk'_pow, one_pow]
  rw [mul_comm]
  conv_rhs => rw [IsLocalization.mk'_eq_mul_mk'_one]
  rfl

lemma normalizePolynomial_cubic (W : WeierstrassCurve k) (i : Fin 3) :
    normalizePolynomial W i W.toProjective.polynomial = 0 := by
  apply HomogeneousLocalization.val_injective
  have hz : Ideal.Quotient.mk (cubicIdeal W) W.toProjective.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [normalizePolynomial_val W i _ (cubic_homogeneous W), hz,
    map_zero, mul_zero, HomogeneousLocalization.val_zero]

/-- The coordinate ring of the affine Weierstrass equation. -/
abbrev affineRing (W : WeierstrassCurve k) := W.toAffine.CoordinateRing
/-- The homomorphism setting the third projective coordinate to one. -/
def dehomogenize (W : WeierstrassCurve k) : homogeneousCoordinateRing W →+* affineRing W :=
  Ideal.Quotient.lift _
    (eval₂Hom (algebraMap k (affineRing W)) ![affineX W, affineY W, 1]) (by
    change cubicIdeal W ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change eval₂Hom (algebraMap k (affineRing W)) ![affineX W, affineY W, 1]
      W.toProjective.polynomial = 0
    simp only [WeierstrassCurve.Projective.polynomial,
      map_add, map_sub, map_mul, map_pow, eval₂Hom_X', eval₂Hom_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_pow,
      mul_one]
    exact WeierstrassCurve.affine_relation W)

@[simp] lemma dehomogenize_coordinate (W : WeierstrassCurve k) (i : Fin 3) :
    dehomogenize W (coordinate W i) = ![affineX W, affineY W, 1] i := by
  simp [dehomogenize, coordinate]
@[simp] lemma dehomogenize_constant (W : WeierstrassCurve k) (a : k) :
    dehomogenize W (algebraMap k (homogeneousCoordinateRing W) a) =
      algebraMap k (affineRing W) a := by
  change dehomogenize W (Ideal.Quotient.mk _ (C a)) = _
  simp [dehomogenize]

/-- The homomorphism from the third projective chart ring to the affine coordinate ring. -/
def fromProjectiveChart (W : WeierstrassCurve k) : chartRing W 2 →+* affineRing W :=
  (Localization.awayLift (dehomogenize W) (coordinate W 2) (by simp)).comp
    (algebraMap (chartRing W 2) (ordinaryChartRing W 2))

lemma fromProjectiveChart_mk (W : WeierstrassCurve k) (n : ℕ)
    (a : homogeneousCoordinateRing W) (ha : a ∈ grading W (n • 1)) :
    fromProjectiveChart W (HomogeneousLocalization.Away.mk (grading W)
      (coordinate_mem W 2) n a ha) = dehomogenize W a := by
  simpa only [fromProjectiveChart, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, dehomogenize_coordinate,
    Matrix.cons_val_two, Matrix.head_cons, one_pow, mul_one] using
    Localization.awayLift_mk (dehomogenize W) (coordinate W 2) a 1 (by simp) n


@[simp] lemma fromProjectiveChart_normalizedCoordinate (W : WeierstrassCurve k) (j : Fin 3) :
    fromProjectiveChart W (normalizedCoordinate W 2 j) = ![affineX W, affineY W, 1] j := by
  rw [normalizedCoordinate, fromProjectiveChart_mk, dehomogenize_coordinate]

@[simp] lemma fromProjectiveChart_constant (W : WeierstrassCurve k) (a : k) :
    fromProjectiveChart W (chartConstant W 2 a) = algebraMap k (affineRing W) a := by
  change fromProjectiveChart W (HomogeneousLocalization.Away.mk (grading W)
    (coordinate_mem W 2) 0 (algebraMap k (homogeneousCoordinateRing W) a) _) = _
  rw [fromProjectiveChart_mk, dehomogenize_constant]

lemma normalized_affine_relation (W : WeierstrassCurve k) :
    normalizedCoordinate W 2 1 ^ 2 +
      (chartConstant W 2 W.a₁ * normalizedCoordinate W 2 0 + chartConstant W 2 W.a₃) *
        normalizedCoordinate W 2 1 -
      (normalizedCoordinate W 2 0 ^ 3 + chartConstant W 2 W.a₂ *
        normalizedCoordinate W 2 0 ^ 2 + chartConstant W 2 W.a₄ *
        normalizedCoordinate W 2 0 + chartConstant W 2 W.a₆) = 0 := by
  have h := normalizePolynomial_cubic W 2
  simp only [normalizePolynomial, WeierstrassCurve.Projective.polynomial,
    map_add, map_sub, map_mul, map_pow, eval₂Hom_X', eval₂Hom_C,
    normalizedCoordinate_self, one_pow, mul_one] at h
  (convert h using 1; ring)

/-- The homomorphism from the affine coordinate ring to the third projective chart ring. -/
def toProjectiveChart (W : WeierstrassCurve k) : affineRing W →+* chartRing W 2 :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (chartConstant W 2) (normalizedCoordinate W 2 0))
    (normalizedCoordinate W 2 1) (by
    simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_add,
      Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom,
      map_add, map_mul, map_pow]
    exact normalized_affine_relation W)

@[simp] lemma toProjectiveChart_affineX (W : WeierstrassCurve k) :
    toProjectiveChart W (affineX W) = normalizedCoordinate W 2 0 := by
  simp [toProjectiveChart, affineX, AdjoinRoot.lift_of]
@[simp] lemma toProjectiveChart_affineY (W : WeierstrassCurve k) :
    toProjectiveChart W (affineY W) = normalizedCoordinate W 2 1 := by
  simp [toProjectiveChart, affineY, AdjoinRoot.lift_root]
@[simp] lemma toProjectiveChart_constant (W : WeierstrassCurve k) (a : k) :
    toProjectiveChart W (algebraMap k (affineRing W) a) = chartConstant W 2 a := by
  change toProjectiveChart W (AdjoinRoot.of W.toAffine.polynomial (Polynomial.C a)) = _
  simp [toProjectiveChart, AdjoinRoot.lift_of]

lemma toProjectiveChart_dehomogenize (W : WeierstrassCurve k)
    (p : MvPolynomial (Fin 3) k) :
    toProjectiveChart W (dehomogenize W (Ideal.Quotient.mk (cubicIdeal W) p)) =
      normalizePolynomial W 2 p := by
  have h : (toProjectiveChart W).comp
      (eval₂Hom (algebraMap k (affineRing W)) ![affineX W, affineY W, 1]) =
      normalizePolynomial W 2 := by
    ext a
    · simp [normalizePolynomial]
    · fin_cases a <;> simp [normalizePolynomial]
  exact congrArg (fun f : MvPolynomial (Fin 3) k →+* chartRing W 2 => f p) h

lemma to_fromProjectiveChart (W : WeierstrassCurve k) (a : chartRing W 2) :
    toProjectiveChart W (fromProjectiveChart W a) = a := by
  obtain ⟨n, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading W) (coordinate_mem W 2) a
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hb
  rw [fromProjectiveChart_mk]
  change toProjectiveChart W (dehomogenize W (Ideal.Quotient.mk (cubicIdeal W) p)) = _
  rw [toProjectiveChart_dehomogenize]
  exact normalizePolynomial_homogeneous W 2 p (by simpa using hp)

lemma from_toProjectiveChart (W : WeierstrassCurve k) (a : affineRing W) :
    fromProjectiveChart W (toProjectiveChart W a) = a := by
  have h : (fromProjectiveChart W).comp (toProjectiveChart W) = RingHom.id _ := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro r
        change fromProjectiveChart W (toProjectiveChart W
          (algebraMap k (affineRing W) r)) = algebraMap k (affineRing W) r
        simp
      · change fromProjectiveChart W (toProjectiveChart W (affineX W)) = affineX W
        simp
    · change fromProjectiveChart W (toProjectiveChart W (affineY W)) = affineY W
      simp
  exact congrArg (fun f : affineRing W →+* affineRing W => f a) h

/-- The existing affine Weierstrass ring is canonically the literal z-chart of the Proj cubic. -/
def affineChartRingEquiv (W : WeierstrassCurve k) : affineRing W ≃+* chartRing W 2 where
  __ := toProjectiveChart W
  invFun := fromProjectiveChart W
  left_inv := from_toProjectiveChart W
  right_inv := to_fromProjectiveChart W

/-- The canonical affine chart map; no arbitrary open immersion is supplied. -/
def affineChart (W : WeierstrassCurve k) : Spec (.of (affineRing W)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (fromProjectiveChart W)) ≫ chart W 2

instance affineChart_open (W : WeierstrassCurve k) : IsOpenImmersion (affineChart W) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (fromProjectiveChart W))) := by
    change IsIso (Scheme.Spec.mapIso (affineChartRingEquiv W).symm.toCommRingCatIso.op).hom
    infer_instance
  unfold affineChart
  infer_instance

lemma affineChart_range (W : WeierstrassCurve k) :
    (affineChart W).opensRange = Proj.basicOpen (grading W) (coordinate W 2) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (fromProjectiveChart W))) := by
    change IsIso (Scheme.Spec.mapIso (affineChartRingEquiv W).symm.toCommRingCatIso.op).hom
    infer_instance
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (chart_range W 2)

@[reassoc] lemma affineChart_structure (W : WeierstrassCurve k) :
    affineChart W ≫ structureMap W =
      Spec.map (CommRingCat.ofHom (algebraMap k (affineRing W))) := by
  rw [affineChart, chart, structureMap, Category.assoc,
    ← Category.assoc _ (Proj.toSpecZero _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact fromProjectiveChart_constant W r


end WeierstrassCurve.Projective
