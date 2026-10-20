/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineComplement
public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.CoordinateTransport
public import Aglib.RingTheory.AdjoinRoot.BivariateTensor
public import Aglib.RingTheory.Localization.Away.MapInverse
public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# The monic infinity chart of the literal Weierstrass cubic

The coordinate-one homogeneous chart is identified with a monic cubic ring.
The two original charts cover the same Proj, and their overlap maps are
(u,v)=(x/y,1/y) and (x,y)=(u/v,1/v), over any commutative ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial TensorProduct
universe u v

namespace WeierstrassCurve.Projective

open MvPolynomial
variable {k : Type u} [CommRing k]

/-- Monic cubic in `u = X/Y`, with coefficient variable `v = Z/Y`. -/
def infinityPolynomial (W : WeierstrassCurve k) : Polynomial (Polynomial k) :=
  Polynomial.X ^ 3 + Polynomial.C (Polynomial.C W.a₂ * Polynomial.X) * Polynomial.X ^ 2 +
    Polynomial.C (Polynomial.C W.a₄ * Polynomial.X ^ 2 - Polynomial.C W.a₁ * Polynomial.X) *
      Polynomial.X +
    Polynomial.C (Polynomial.C W.a₆ * Polynomial.X ^ 3 -
      Polynomial.C W.a₃ * Polynomial.X ^ 2 - Polynomial.X)

lemma infinityPolynomial_monic (W : WeierstrassCurve k) :
    (infinityPolynomial W).Monic := by
  simpa only [infinityPolynomial, Cubic.toPoly, Polynomial.C_1, one_mul] using
    (Cubic.monic_of_a_eq_one (P :=
      ⟨1, Polynomial.C W.a₂ * Polynomial.X,
        Polynomial.C W.a₄ * Polynomial.X ^ 2 - Polynomial.C W.a₁ * Polynomial.X,
        Polynomial.C W.a₆ * Polynomial.X ^ 3 - Polynomial.C W.a₃ * Polynomial.X ^ 2 -
          Polynomial.X⟩) rfl)

/-- The monic cubic coordinate ring of the chart where the homogeneous `Y` coordinate is nonzero. -/
abbrev infinityRing (W : WeierstrassCurve k) := AdjoinRoot (infinityPolynomial W)
/-- The infinity-chart coordinate `u = X/Y`, realized as the adjoined root. -/
def infinityU (W : WeierstrassCurve k) : infinityRing W :=
  AdjoinRoot.root (infinityPolynomial W)
/-- The infinity-chart coordinate `v = Z/Y`, realized as the base polynomial variable. -/
def infinityV (W : WeierstrassCurve k) : infinityRing W :=
  AdjoinRoot.of (infinityPolynomial W) Polynomial.X

lemma infinity_relation (W : WeierstrassCurve k) :
    infinityV W + algebraMap k (infinityRing W) W.a₁ * infinityU W * infinityV W +
      algebraMap k (infinityRing W) W.a₃ * infinityV W ^ 2 -
      (infinityU W ^ 3 + algebraMap k (infinityRing W) W.a₂ * infinityU W ^ 2 * infinityV W +
        algebraMap k (infinityRing W) W.a₄ * infinityU W * infinityV W ^ 2 +
        algebraMap k (infinityRing W) W.a₆ * infinityV W ^ 3) = 0 := by
  have h := AdjoinRoot.eval₂_root (infinityPolynomial W)
  conv_lhs at h => arg 3; unfold infinityPolynomial
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    map_sub, map_mul, map_pow] at h
  change infinityU W ^ 3 + algebraMap k (infinityRing W) W.a₂ * infinityV W * infinityU W ^ 2 +
    (algebraMap k (infinityRing W) W.a₄ * infinityV W ^ 2 -
      algebraMap k (infinityRing W) W.a₁ * infinityV W) * infinityU W +
    (algebraMap k (infinityRing W) W.a₆ * infinityV W ^ 3 -
      algebraMap k (infinityRing W) W.a₃ * infinityV W ^ 2 - infinityV W) = 0 at h
  linear_combination -h

/-- Dehomogenization of the cubic coordinate ring at `Y = 1` into the monic infinity ring. -/
def infinityDehomogenize (W : WeierstrassCurve k) :
    homogeneousCoordinateRing W →+* infinityRing W :=
  Ideal.Quotient.lift _
    (eval₂Hom (algebraMap k (infinityRing W)) ![infinityU W, 1, infinityV W]) (by
    change cubicIdeal W ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change eval₂Hom (algebraMap k (infinityRing W)) ![infinityU W, 1, infinityV W]
      W.toProjective.polynomial = 0
    simpa only [WeierstrassCurve.Projective.polynomial,
      map_add, map_sub, map_mul, map_pow, eval₂Hom_X', eval₂Hom_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_pow, mul_one, one_mul] using infinity_relation W)

@[simp] lemma infinityDehomogenize_coordinate (W : WeierstrassCurve k) (i : Fin 3) :
    infinityDehomogenize W (coordinate W i) = ![infinityU W, 1, infinityV W] i := by
  simp [infinityDehomogenize, coordinate]
@[simp] lemma infinityDehomogenize_constant (W : WeierstrassCurve k) (a : k) :
    infinityDehomogenize W (algebraMap k (homogeneousCoordinateRing W) a) =
      algebraMap k (infinityRing W) a := by
  change infinityDehomogenize W (Ideal.Quotient.mk _ (C a)) = _
  simp [infinityDehomogenize]

/-- The map from the homogeneous chart at `Y` to the monic infinity ring. -/
def fromInfinityProjectiveChart (W : WeierstrassCurve k) : chartRing W 1 →+* infinityRing W :=
  (Localization.awayLift (infinityDehomogenize W) (coordinate W 1) (by simp)).comp
    (algebraMap (chartRing W 1) (ordinaryChartRing W 1))

lemma fromInfinityProjectiveChart_mk (W : WeierstrassCurve k) (n : ℕ)
    (a : homogeneousCoordinateRing W) (ha : a ∈ grading W (n • 1)) :
    fromInfinityProjectiveChart W (HomogeneousLocalization.Away.mk (grading W)
      (coordinate_mem W 1) n a ha) = infinityDehomogenize W a := by
  simpa only [fromInfinityProjectiveChart, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    infinityDehomogenize_coordinate, Matrix.cons_val_one, Matrix.head_cons, one_pow, mul_one] using
    Localization.awayLift_mk (infinityDehomogenize W) (coordinate W 1) a 1 (by simp) n

@[simp] lemma fromInfinityProjectiveChart_normalizedCoordinate
    (W : WeierstrassCurve k) (j : Fin 3) :
    fromInfinityProjectiveChart W (normalizedCoordinate W 1 j) =
      ![infinityU W, 1, infinityV W] j := by
  rw [normalizedCoordinate, fromInfinityProjectiveChart_mk, infinityDehomogenize_coordinate]

@[simp] lemma fromInfinityProjectiveChart_constant (W : WeierstrassCurve k) (a : k) :
    fromInfinityProjectiveChart W (chartConstant W 1 a) = algebraMap k (infinityRing W) a := by
  change fromInfinityProjectiveChart W (HomogeneousLocalization.Away.mk (grading W)
    (coordinate_mem W 1) 0 (algebraMap k (homogeneousCoordinateRing W) a) _) = _
  rw [fromInfinityProjectiveChart_mk, infinityDehomogenize_constant]

lemma normalized_infinity_relation (W : WeierstrassCurve k) :
    Polynomial.eval₂
      (Polynomial.eval₂RingHom (chartConstant W 1) (normalizedCoordinate W 1 2))
      (normalizedCoordinate W 1 0) (infinityPolynomial W) = 0 := by
  have h := normalizePolynomial_cubic W 1
  simp only [normalizePolynomial, WeierstrassCurve.Projective.polynomial,
    map_add, map_sub, map_mul, map_pow, eval₂Hom_X', eval₂Hom_C,
    normalizedCoordinate_self, one_pow, mul_one, one_mul] at h
  simp only [infinityPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_eval₂RingHom, map_sub, map_mul, map_pow]
  linear_combination -h

/-- The map from the monic infinity ring to the homogeneous chart at `Y`. -/
def toInfinityProjectiveChart (W : WeierstrassCurve k) : infinityRing W →+* chartRing W 1 :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (chartConstant W 1) (normalizedCoordinate W 1 2))
    (normalizedCoordinate W 1 0) (normalized_infinity_relation W)

@[simp] lemma toInfinityProjectiveChart_infinityU (W : WeierstrassCurve k) :
    toInfinityProjectiveChart W (infinityU W) = normalizedCoordinate W 1 0 := by
  simp [toInfinityProjectiveChart, infinityU, AdjoinRoot.lift_root]
@[simp] lemma toInfinityProjectiveChart_infinityV (W : WeierstrassCurve k) :
    toInfinityProjectiveChart W (infinityV W) = normalizedCoordinate W 1 2 := by
  simp [toInfinityProjectiveChart, infinityV, AdjoinRoot.lift_of]
@[simp] lemma toInfinityProjectiveChart_constant (W : WeierstrassCurve k) (a : k) :
    toInfinityProjectiveChart W (algebraMap k (infinityRing W) a) = chartConstant W 1 a := by
  change toInfinityProjectiveChart W
    (AdjoinRoot.of (infinityPolynomial W) (Polynomial.C a)) = _
  simp [toInfinityProjectiveChart, AdjoinRoot.lift_of]

lemma toInfinityProjectiveChart_dehomogenize (W : WeierstrassCurve k)
    (p : MvPolynomial (Fin 3) k) :
    toInfinityProjectiveChart W (infinityDehomogenize W (Ideal.Quotient.mk (cubicIdeal W) p)) =
      normalizePolynomial W 1 p := by
  have h : (toInfinityProjectiveChart W).comp
      (eval₂Hom (algebraMap k (infinityRing W)) ![infinityU W, 1, infinityV W]) =
      normalizePolynomial W 1 := by
    ext a
    · simp [normalizePolynomial]
    · fin_cases a <;> simp [normalizePolynomial]
  exact congrArg (fun f : MvPolynomial (Fin 3) k →+* chartRing W 1 => f p) h

lemma to_fromInfinityProjectiveChart (W : WeierstrassCurve k) (a : chartRing W 1) :
    toInfinityProjectiveChart W (fromInfinityProjectiveChart W a) = a := by
  obtain ⟨n, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading W) (coordinate_mem W 1) a
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hb
  rw [fromInfinityProjectiveChart_mk]
  change toInfinityProjectiveChart W
    (infinityDehomogenize W (Ideal.Quotient.mk (cubicIdeal W) p)) = _
  rw [toInfinityProjectiveChart_dehomogenize]
  exact normalizePolynomial_homogeneous W 1 p (by simpa using hp)

lemma from_toInfinityProjectiveChart (W : WeierstrassCurve k) (a : infinityRing W) :
    fromInfinityProjectiveChart W (toInfinityProjectiveChart W a) = a := by
  have h : (fromInfinityProjectiveChart W).comp (toInfinityProjectiveChart W) = RingHom.id _ := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro r
        change fromInfinityProjectiveChart W (toInfinityProjectiveChart W
          (algebraMap k (infinityRing W) r)) = algebraMap k (infinityRing W) r
        simp
      · change fromInfinityProjectiveChart W (toInfinityProjectiveChart W (infinityV W)) =
          infinityV W
        simp
    · change fromInfinityProjectiveChart W (toInfinityProjectiveChart W (infinityU W)) =
        infinityU W
      simp
  exact congrArg (fun f : infinityRing W →+* infinityRing W => f a) h

/-- The monic infinity-chart ring is exactly the coordinate-1 open in the existing Proj. -/
def infinityChartRingEquiv (W : WeierstrassCurve k) : infinityRing W ≃+* chartRing W 1 where
  __ := toInfinityProjectiveChart W
  invFun := fromInfinityProjectiveChart W
  left_inv := from_toInfinityProjectiveChart W
  right_inv := to_fromInfinityProjectiveChart W

/-- The explicit infinity chart of the existing projective cubic. -/
def infinityAffineChart (W : WeierstrassCurve k) : Spec (.of (infinityRing W)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (fromInfinityProjectiveChart W)) ≫ chart W 1

/-- The monic infinity chart maps openly into the original projective Weierstrass cubic. -/
instance infinityAffineChart_open (W : WeierstrassCurve k) :
    IsOpenImmersion (infinityAffineChart W) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (fromInfinityProjectiveChart W))) := by
    change IsIso (Scheme.Spec.mapIso (infinityChartRingEquiv W).symm.toCommRingCatIso.op).hom
    infer_instance
  unfold infinityAffineChart
  infer_instance

lemma infinityAffineChart_range (W : WeierstrassCurve k) :
    (infinityAffineChart W).opensRange = Proj.basicOpen (grading W) (coordinate W 1) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (fromInfinityProjectiveChart W))) := by
    change IsIso (Scheme.Spec.mapIso (infinityChartRingEquiv W).symm.toCommRingCatIso.op).hom
    infer_instance
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (chart_range W 1)

@[reassoc] lemma infinityAffineChart_structure (W : WeierstrassCurve k) :
    infinityAffineChart W ≫ structureMap W =
      Spec.map (CommRingCat.ofHom (algebraMap k (infinityRing W))) := by
  rw [infinityAffineChart, chart, structureMap, Category.assoc,
    ← Category.assoc _ (Proj.toSpecZero _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact fromInfinityProjectiveChart_constant W r

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

variable {k : Type u} [CommRing k]

/-- The monic infinity ring is free over the polynomial ring in `v`. -/
instance infinityRing_free_polynomial (W : WeierstrassCurve k) :
    Module.Free (Polynomial k) (infinityRing W) :=
  (infinityPolynomial_monic W).free_adjoinRoot

/-- The monic infinity ring is finite over the polynomial ring in `v`. -/
instance infinityRing_finite_polynomial (W : WeierstrassCurve k) :
    Module.Finite (Polynomial k) (infinityRing W) :=
  (infinityPolynomial_monic W).finite_adjoinRoot

/-- The monic infinity ring is free over the coefficient ring. -/
instance infinityRing_free (W : WeierstrassCurve k) : Module.Free k (infinityRing W) :=
  .trans (S := Polynomial k)

/-- The monic infinity ring is flat over the coefficient ring. -/
instance infinityRing_flat (W : WeierstrassCurve k) : Module.Flat k (infinityRing W) :=
  inferInstance

/-- The infinity chart and ordinary affine chart together cover the literal Proj. -/
lemma infinity_affine_cover (W : WeierstrassCurve k) :
    (infinityAffineChart W).opensRange ⊔ (affineChart W).opensRange = ⊤ := by
  apply top_unique
  intro p _
  classical
  by_cases hz : coordinate W 2 ∈ p.asHomogeneousIdeal
  · exact Or.inl (by
      rw [infinityAffineChart_range]
      exact coordinate_y_not_mem_of_z_mem W p hz)
  · exact Or.inr (by
      rw [affineChart_range]
      exact hz)

/-- A two-element open cover using the explicit monic quotient charts. -/
def monicChartCover (W : WeierstrassCurve k) : (scheme W).OpenCover :=
  Scheme.Cover.mkOfCovers Bool
    (fun | false => Spec (.of (infinityRing W)) | true => Spec (.of (affineRing W)))
    (fun | false => infinityAffineChart W | true => affineChart W)
    (by
      intro p
      have hp : p ∈ (infinityAffineChart W).opensRange ⊔ (affineChart W).opensRange := by
        rw [infinity_affine_cover]
        trivial
      rcases hp with h | h
      · obtain ⟨q, hq⟩ := h
        exact ⟨false, q, hq⟩
      · obtain ⟨q, hq⟩ := h
        exact ⟨true, q, hq⟩)
    (by intro b; cases b <;> infer_instance)

/-- Flatness is proved for the existing structural morphism over every commutative ring. -/
instance structureMap_flat (W : WeierstrassCurve k) : Flat (structureMap W) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Flat) (monicChartCover W)).mpr
  intro b
  cases b
  · change Flat (infinityAffineChart W ≫ structureMap W)
    rw [infinityAffineChart_structure, Flat.SpecMap_iff]
    change (algebraMap k (infinityRing W)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · change Flat (affineChart W ≫ structureMap W)
    rw [affineChart_structure, Flat.SpecMap_iff]
    change (algebraMap k (affineRing W)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- Evaluation of the infinity ring at coordinates `(x, z)` satisfying its equation under `f`. -/
def infinityLift (W : WeierstrassCurve R) (f : R →+* S) (x z : S)
    (h : z + f W.a₁ * x * z + f W.a₃ * z ^ 2 -
      (x ^ 3 + f W.a₂ * x ^ 2 * z + f W.a₄ * x * z ^ 2 + f W.a₆ * z ^ 3) = 0) :
    infinityRing W →+* S :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom f z) x (by
    simp only [infinityPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.coe_eval₂RingHom, map_sub, map_mul, map_pow]
    linear_combination -h)

@[simp] lemma infinityLift_u (W : WeierstrassCurve R) (f : R →+* S) (x z : S) (h) :
    infinityLift W f x z h (infinityU W) = x := by
  simp [infinityLift, infinityU, AdjoinRoot.lift_root]
@[simp] lemma infinityLift_v (W : WeierstrassCurve R) (f : R →+* S) (x z : S) (h) :
    infinityLift W f x z h (infinityV W) = z := by
  simp [infinityLift, infinityV, AdjoinRoot.lift_of]
@[simp] lemma infinityLift_constant (W : WeierstrassCurve R) (f : R →+* S)
    (x z : S) (h) (r : R) :
    infinityLift W f x z h (algebraMap R (infinityRing W) r) = f r := by
  change infinityLift W f x z h (AdjoinRoot.of _ (Polynomial.C r)) = _
  simp [infinityLift, AdjoinRoot.lift_of]

/-- The source RingHom lift delegates to the native affine algebra lift for the same f. -/
def affineRingLift (W : WeierstrassCurve R) (f : R →+* S) (x y : S)
    (h : y ^ 2 + (f W.a₁ * x + f W.a₃) * y -
      (x ^ 3 + f W.a₂ * x ^ 2 + f W.a₄ * x + f W.a₆) = 0) : affineRing W →+* S :=
  letI : Algebra R S := f.toAlgebra
  (WeierstrassCurve.affineLift W x y (by
    simpa only [RingHom.algebraMap_toAlgebra, add_mul, add_assoc] using h)).toRingHom

@[simp] lemma affineRingLift_x (W : WeierstrassCurve R) (f : R →+* S) (x y : S) (h) :
    affineRingLift W f x y h (affineX W) = x := by simp [affineRingLift]
@[simp] lemma affineRingLift_y (W : WeierstrassCurve R) (f : R →+* S) (x y : S) (h) :
    affineRingLift W f x y h (affineY W) = y := by simp [affineRingLift]
@[simp] lemma affineRingLift_constant (W : WeierstrassCurve R) (f : R →+* S)
    (x y : S) (h) (r : R) :
    affineRingLift W f x y h (algebraMap R (affineRing W) r) = f r := by
  simp [affineRingLift, RingHom.algebraMap_toAlgebra]

lemma infinityLift_relation (a₁ a₂ a₃ a₄ a₆ x y t : S)
    (h : y ^ 2 + (a₁ * x + a₃) * y - (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) = 0)
    (hy : y * t = 1) :
    t + a₁ * (x * t) * t + a₃ * t ^ 2 -
      ((x * t) ^ 3 + a₂ * (x * t) ^ 2 * t + a₄ * (x * t) * t ^ 2 + a₆ * t ^ 3) = 0 := by
  linear_combination h * t ^ 3 - (hy) * (t * (y * t + 1) + a₁ * x * t ^ 2 + a₃ * t ^ 2)

lemma affineRingLift_relation (a₁ a₂ a₃ a₄ a₆ x z t : S)
    (h : z + a₁ * x * z + a₃ * z ^ 2 -
      (x ^ 3 + a₂ * x ^ 2 * z + a₄ * x * z ^ 2 + a₆ * z ^ 3) = 0)
    (hz : z * t = 1) :
    t ^ 2 + (a₁ * (x * t) + a₃) * t -
      ((x * t) ^ 3 + a₂ * (x * t) ^ 2 + a₄ * (x * t) + a₆) = 0 := by
  linear_combination h * t ^ 3 + hz * (-t ^ 2 - a₁ * x * t ^ 2 -
    a₃ * t * (z * t + 1) + a₂ * x ^ 2 * t ^ 2 + a₄ * x * t * (z * t + 1) +
    a₆ * ((z * t) ^ 2 + z * t + 1))

/-- The affine coordinate ring localized where the affine `y` coordinate is invertible. -/
abbrev affineOverlapRing (W : WeierstrassCurve R) := Localization.Away (affineY W)
/-- The infinity coordinate ring localized where `v = Z/Y` is invertible. -/
abbrev infinityOverlapRing (W : WeierstrassCurve R) := Localization.Away (infinityV W)

/-- The infinity-ring map to the affine overlap given by `(u, v) = (x/y, 1/y)`. -/
def infinityToAffineOverlap (W : WeierstrassCurve R) : infinityRing W →+* affineOverlapRing W :=
  infinityLift W (algebraMap R _) (algebraMap _ _ (affineX W) *
    IsLocalization.Away.invSelf (affineY W)) (IsLocalization.Away.invSelf (affineY W)) (by
      apply infinityLift_relation
      · have h := congrArg (algebraMap (affineRing W) (affineOverlapRing W)) (affine_relation W)
        simpa only [map_add, map_sub, map_mul, map_pow, map_zero, add_mul, add_assoc,
          ← IsScalarTower.algebraMap_apply] using h
      · exact IsLocalization.Away.mul_invSelf _)

/-- The affine-ring map to the infinity overlap given by `(x, y) = (u/v, 1/v)`. -/
def affineToInfinityOverlap (W : WeierstrassCurve R) : affineRing W →+* infinityOverlapRing W :=
  affineRingLift W (algebraMap R _) (algebraMap _ _ (infinityU W) *
    IsLocalization.Away.invSelf (infinityV W)) (IsLocalization.Away.invSelf (infinityV W)) (by
      apply affineRingLift_relation
      · have h := congrArg (algebraMap (infinityRing W) (infinityOverlapRing W))
          (infinity_relation W)
        simpa only [map_add, map_sub, map_mul, map_pow, map_zero, add_mul, add_assoc,
          ← IsScalarTower.algebraMap_apply] using h
      · exact IsLocalization.Away.mul_invSelf _)


@[simp] lemma infinityToAffineOverlap_u (W : WeierstrassCurve R) :
    infinityToAffineOverlap W (infinityU W) = algebraMap _ _ (affineX W) *
      IsLocalization.Away.invSelf (affineY W) := by simp [infinityToAffineOverlap]
@[simp] lemma infinityToAffineOverlap_v (W : WeierstrassCurve R) :
    infinityToAffineOverlap W (infinityV W) = IsLocalization.Away.invSelf (affineY W) := by
  simp [infinityToAffineOverlap]
@[simp] lemma infinityToAffineOverlap_constant (W : WeierstrassCurve R) (r : R) :
    infinityToAffineOverlap W (algebraMap R (infinityRing W) r) = algebraMap R _ r := by
  simp [infinityToAffineOverlap]
@[simp] lemma affineToInfinityOverlap_x (W : WeierstrassCurve R) :
    affineToInfinityOverlap W (affineX W) = algebraMap _ _ (infinityU W) *
      IsLocalization.Away.invSelf (infinityV W) := by simp [affineToInfinityOverlap]
@[simp] lemma affineToInfinityOverlap_y (W : WeierstrassCurve R) :
    affineToInfinityOverlap W (affineY W) = IsLocalization.Away.invSelf (infinityV W) := by
  simp [affineToInfinityOverlap]
@[simp] lemma affineToInfinityOverlap_constant (W : WeierstrassCurve R) (r : R) :
    affineToInfinityOverlap W (algebraMap R (affineRing W) r) = algebraMap R _ r := by
  simp [affineToInfinityOverlap]


/-- The reciprocal-coordinate map from the localized infinity ring to the localized affine ring. -/
def infinityOverlapToAffine (W : WeierstrassCurve R) :
    infinityOverlapRing W →+* affineOverlapRing W :=
  Localization.awayLift (infinityToAffineOverlap W) (infinityV W) (by
    rw [infinityToAffineOverlap_v]
    exact Localization.Away.invSelf_isUnit _)

/-- The reciprocal-coordinate map from the localized affine ring to the localized infinity ring. -/
def affineOverlapToInfinity (W : WeierstrassCurve R) :
    affineOverlapRing W →+* infinityOverlapRing W :=
  Localization.awayLift (affineToInfinityOverlap W) (affineY W) (by
    rw [affineToInfinityOverlap_y]
    exact Localization.Away.invSelf_isUnit _)

@[simp] lemma infinityOverlapToAffine_map (W : WeierstrassCurve R) (a : infinityRing W) :
    infinityOverlapToAffine W (algebraMap _ _ a) = infinityToAffineOverlap W a := by
  simp [infinityOverlapToAffine, Localization.awayLift, IsLocalization.Away.lift_eq]
@[simp] lemma affineOverlapToInfinity_map (W : WeierstrassCurve R) (a : affineRing W) :
    affineOverlapToInfinity W (algebraMap _ _ a) = affineToInfinityOverlap W a := by
  simp [affineOverlapToInfinity, Localization.awayLift, IsLocalization.Away.lift_eq]


@[simp] lemma infinityOverlapToAffine_invSelf (W : WeierstrassCurve R) :
    infinityOverlapToAffine W (IsLocalization.Away.invSelf (infinityV W)) =
      algebraMap _ _ (affineY W) := by
  apply Localization.Away.map_invSelf_of_mul
  simp only [infinityOverlapToAffine_map, infinityToAffineOverlap_v]
  rw [mul_comm, IsLocalization.Away.mul_invSelf]
@[simp] lemma affineOverlapToInfinity_invSelf (W : WeierstrassCurve R) :
    affineOverlapToInfinity W (IsLocalization.Away.invSelf (affineY W)) =
      algebraMap _ _ (infinityV W) := by
  apply Localization.Away.map_invSelf_of_mul
  simp only [affineOverlapToInfinity_map, affineToInfinityOverlap_y]
  rw [mul_comm, IsLocalization.Away.mul_invSelf]

@[simp] lemma infinityOverlapToAffine_constant (W : WeierstrassCurve R) (r : R) :
    infinityOverlapToAffine W (algebraMap R _ r) = algebraMap R _ r := by
  rw [IsScalarTower.algebraMap_apply R (infinityRing W), infinityOverlapToAffine_map,
    infinityToAffineOverlap_constant]
@[simp] lemma affineOverlapToInfinity_constant (W : WeierstrassCurve R) (r : R) :
    affineOverlapToInfinity W (algebraMap R _ r) = algebraMap R _ r := by
  rw [IsScalarTower.algebraMap_apply R (affineRing W), affineOverlapToInfinity_map,
    affineToInfinityOverlap_constant]

lemma overlap_left_inv (W : WeierstrassCurve R) :
    (affineOverlapToInfinity W).comp (infinityOverlapToAffine W) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (infinityV W))
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      change affineOverlapToInfinity W (infinityOverlapToAffine W
        (algebraMap R _ r)) = algebraMap R _ r
      simp
    · change affineOverlapToInfinity W (infinityOverlapToAffine W
        (algebraMap _ _ (infinityV W))) = algebraMap _ _ (infinityV W)
      simp
  · change affineOverlapToInfinity W (infinityOverlapToAffine W
      (algebraMap _ _ (infinityU W))) = algebraMap _ _ (infinityU W)
    simp only [infinityOverlapToAffine_map, infinityToAffineOverlap_u, map_mul,
      affineOverlapToInfinity_map, affineToInfinityOverlap_x, affineOverlapToInfinity_invSelf]
    rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf _),
      IsLocalization.Away.mul_invSelf, mul_one]

lemma overlap_right_inv (W : WeierstrassCurve R) :
    (infinityOverlapToAffine W).comp (affineOverlapToInfinity W) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (affineY W))
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      change infinityOverlapToAffine W (affineOverlapToInfinity W
        (algebraMap R _ r)) = algebraMap R _ r
      simp
    · change infinityOverlapToAffine W (affineOverlapToInfinity W
        (algebraMap _ _ (affineX W))) = algebraMap _ _ (affineX W)
      simp only [affineOverlapToInfinity_map, affineToInfinityOverlap_x, map_mul,
        infinityOverlapToAffine_map, infinityToAffineOverlap_u, infinityOverlapToAffine_invSelf]
      rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf _),
        IsLocalization.Away.mul_invSelf, mul_one]
  · change infinityOverlapToAffine W (affineOverlapToInfinity W
      (algebraMap _ _ (affineY W))) = algebraMap _ _ (affineY W)
    simp

/-- Literal coordinate overlap: `u = x/y`, `v = 1/y`, with inverse `x = u/v`, `y = 1/v`. -/
def infinityAffineOverlapEquiv (W : WeierstrassCurve R) :
    infinityOverlapRing W ≃+* affineOverlapRing W where
  __ := infinityOverlapToAffine W
  invFun := affineOverlapToInfinity W
  left_inv := by
    intro a
    change ((affineOverlapToInfinity W).comp (infinityOverlapToAffine W)) a = a
    rw [overlap_left_inv, RingHom.id_apply]
  right_inv := by
    intro a
    change ((infinityOverlapToAffine W).comp (affineOverlapToInfinity W)) a = a
    rw [overlap_right_inv, RingHom.id_apply]

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

variable {R S : Type u} [CommRing R] [CommRing S]

lemma infinityPolynomial_map (W : WeierstrassCurve R) (f : R →+* S) :
    (infinityPolynomial W).map (Polynomial.mapRingHom f) = infinityPolynomial (W.map f) := by
  simp [infinityPolynomial, WeierstrassCurve.map]

lemma affinePolynomial_map (W : WeierstrassCurve R) (f : R →+* S) :
    W.toAffine.polynomial.map (Polynomial.mapRingHom f) = (W.map f).toAffine.polynomial := by
  simp [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.map]

variable [Algebra R S]

/-- The actual infinity chart commutes with coefficient base change. -/
def infinityRingBaseChangeEquiv (W : WeierstrassCurve R) :
    S ⊗[R] infinityRing W ≃ₐ[S] infinityRing (W.baseChange S) :=
  AdjoinRoot.bivariateTensorEquiv (infinityPolynomial W) (infinityPolynomial (W.baseChange S))
    (infinityPolynomial_map W (algebraMap R S))

end WeierstrassCurve.Projective

/- Migration prerequisite: exact consumed parts of PointedResolution.Weierstrass.Charts.
Frozen R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 6c0aed447ddc2370e521c38cece435c0bb428963c203b36d9879205fb2f9480c.
The existing affine tensor equivalence and coordinate ring are reused literally. -/
