/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.Coordinates
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination

/-!
# The affine parameterization of a critical cubic

The literal Weierstrass equation with a₃ = a₄ = a₆ = 0 has polynomial
parameterization X = T² + aT − b and Y = TX. Degree parity proves injectivity
of its coordinate-ring map. Its actual origin fibre is identified on sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

open WeierstrassCurve

namespace WeierstrassCurve.CriticalCubic

variable (k : Type u) [Field k] (a b : k)

/-- The Weierstrass equation with coefficient tuple `(a, b, 0, 0, 0)`. -/
def equation : WeierstrassCurve k where
  a₁ := a
  a₂ := b
  a₃ := 0
  a₄ := 0
  a₆ := 0

/-- The polynomial `T² + aT - b` giving the affine `x` coordinate of the normalization. -/
def xPolynomial : k[X] := X ^ 2 + C a * X - C b
/-- The polynomial `T(T² + aT - b)` giving the affine `y` coordinate of the normalization. -/
def yPolynomial : k[X] := X * xPolynomial k a b

lemma parameter_relation :
    yPolynomial k a b ^ 2 + C a * xPolynomial k a b * yPolynomial k a b -
      (xPolynomial k a b ^ 3 + C b * xPolynomial k a b ^ 2) = 0 := by
  dsimp [xPolynomial, yPolynomial]
  ring

lemma polynomial_eval_zero : (equation k a b).toAffine.polynomial.eval₂
    (aeval (xPolynomial k a b)).toRingHom (yPolynomial k a b) = 0 := by
  simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_add,
    Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, map_add, map_mul, map_pow]
  simpa [equation, WeierstrassCurve.toAffine, map_zero, zero_mul, add_zero,
    aeval_C, aeval_X] using parameter_relation k a b

/-- The actual affine coordinate-ring map. -/
def coordinateMap : (equation k a b).toAffine.CoordinateRing →ₐ[k] k[X] :=
  WeierstrassCurve.affineLift (equation k a b) (xPolynomial k a b) (yPolynomial k a b)
    (by simpa [equation, Polynomial.algebraMap_eq] using parameter_relation k a b)

/-- The native lift is the same literal AdjoinRoot map as the source parameterization. -/
lemma coordinateMap_eq_liftAlgHom : coordinateMap k a b =
    AdjoinRoot.liftAlgHom _ (aeval (xPolynomial k a b)) (yPolynomial k a b)
      (polynomial_eval_zero k a b) := rfl

@[simp] lemma coordinateMap_X :
    coordinateMap k a b (WeierstrassCurve.affineX (equation k a b)) =
      xPolynomial k a b := by
  simp [coordinateMap]

@[simp] lemma coordinateMap_Y :
    coordinateMap k a b (WeierstrassCurve.affineY (equation k a b)) =
      yPolynomial k a b := by
  simp [coordinateMap]

lemma xPolynomial_natDegree : (xPolynomial k a b).natDegree = 2 := by
  unfold xPolynomial
  compute_degree <;> norm_num

lemma xPolynomial_ne_zero : xPolynomial k a b ≠ 0 := by
  intro h
  have hd := xPolynomial_natDegree k a b
  rw [h, natDegree_zero] at hd
  omega

lemma yPolynomial_natDegree : (yPolynomial k a b).natDegree = 3 := by
  rw [yPolynomial, natDegree_mul X_ne_zero (xPolynomial_ne_zero k a b),
    natDegree_X, xPolynomial_natDegree]

lemma comp_x_eq_zero_iff (p : k[X]) : p.comp (xPolynomial k a b) = 0 ↔ p = 0 := by
  have hn : xPolynomial k a b ≠ C ((xPolynomial k a b).coeff 0) := by
    intro h
    have hd := congrArg Polynomial.natDegree h
    norm_num [xPolynomial_natDegree] at hd
  rw [comp_eq_zero_iff]
  simp only [hn, and_false, or_false]

/-- Even and odd degrees force uniqueness of the actual two-coordinate normal form. -/
lemma parameter_normal_form_eq_zero (p q : k[X]) :
    p.comp (xPolynomial k a b) + yPolynomial k a b * q.comp (xPolynomial k a b) = 0 ↔
      p = 0 ∧ q = 0 := by
  constructor
  · intro h
    have hq : q = 0 := by
      by_contra hq
      have hqc : q.comp (xPolynomial k a b) ≠ 0 := mt (comp_x_eq_zero_iff k a b q).mp hq
      have hy : yPolynomial k a b ≠ 0 := mul_ne_zero X_ne_zero (xPolynomial_ne_zero k a b)
      have hd := congrArg Polynomial.natDegree (eq_neg_of_add_eq_zero_left h)
      rw [natDegree_comp, natDegree_neg, natDegree_mul hy hqc,
        yPolynomial_natDegree, natDegree_comp, xPolynomial_natDegree] at hd
      omega
    subst q
    simp only [Polynomial.zero_comp, mul_zero, add_zero] at h
    exact ⟨(comp_x_eq_zero_iff k a b p).mp h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp


lemma coordinateMap_injective : Function.Injective (coordinateMap k a b) := by
  apply (injective_iff_map_eq_zero (coordinateMap k a b)).mpr
  intro z hz
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq z
  have hpq : p = 0 ∧ q = 0 := by
    apply (parameter_normal_form_eq_zero k a b p q).mp
    simp only [WeierstrassCurve.Affine.CoordinateRing.smul, map_add, map_mul,
      mul_one, coordinateMap_eq_liftAlgHom, WeierstrassCurve.Affine.CoordinateRing.mk,
      AdjoinRoot.liftAlgHom_mk, Polynomial.eval₂_C, Polynomial.eval₂_X] at hz
    simpa only [AlgHom.coe_toRingHom, ← comp_eq_aeval, mul_comm] using hz
  rw [hpq.1, hpq.2]
  simp
local notation "A" => WeierstrassCurve.Affine.CoordinateRing
  (WeierstrassCurve.toAffine (equation k a b))

/-- The actual finite morphism of affine schemes induced by normalization. -/
def affineNormalization : Spec (.of k[X]) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (coordinateMap k a b).toRingHom)
/-- The singular-origin section's literal coordinate homomorphism. -/
def originMap : A →ₐ[k] k :=
  WeierstrassCurve.affineLift (equation k a b) 0 0 (by simp [equation])

@[simp] lemma originMap_X : originMap k a b
    (WeierstrassCurve.affineX (equation k a b)) = 0 := by
  simp [originMap]

@[simp] lemma originMap_Y : originMap k a b
    (WeierstrassCurve.affineY (equation k a b)) = 0 := by
  simp [originMap]

lemma eval_coordinateMap_eq_origin_iff (t : k) :
    (aeval t).comp (coordinateMap k a b) = originMap k a b ↔
      t ^ 2 + a * t - b = 0 := by
  constructor
  · intro h
    have hx := congrArg (fun f : A →ₐ[k] k =>
      f (WeierstrassCurve.affineX (equation k a b))) h
    simpa [xPolynomial] using hx
  · intro ht
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change (aeval t) (coordinateMap k a b
        (WeierstrassCurve.affineX (equation k a b))) =
        originMap k a b (WeierstrassCurve.affineX (equation k a b))
      simpa [xPolynomial] using ht
    · change (aeval t) (coordinateMap k a b
        (WeierstrassCurve.affineY (equation k a b))) =
        originMap k a b (WeierstrassCurve.affineY (equation k a b))
      simp [yPolynomial, xPolynomial, ht]

/-- A literal parameter section of the affine line. -/
def parameterSection (t : k) : Spec (.of k) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (aeval t).toRingHom)

/-- The literal origin section of the actual affine cubic. -/
def originSection : Spec (.of k) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (originMap k a b).toRingHom)

/-- The exact scheme-morphism triangle characterizing the rational origin fibre. -/
lemma parameterSection_comp_eq_origin_iff (t : k) :
    parameterSection k t ≫ affineNormalization k a b = originSection k a b ↔
      t ^ 2 + a * t - b = 0 := by
  change Spec.map (CommRingCat.ofHom (aeval t).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (coordinateMap k a b).toRingHom) = _ ↔ _
  rw [← Spec.map_comp, originSection, Spec.map_inj]
  change CommRingCat.ofHom (((aeval t).comp (coordinateMap k a b)).toRingHom) =
    CommRingCat.ofHom (originMap k a b).toRingHom ↔ _
  rw [CommRingCat.hom_ext_iff]
  exact (AlgHom.coe_ringHom_injective.eq_iff).trans
    (eval_coordinateMap_eq_origin_iff k a b t)
end WeierstrassCurve.CriticalCubic

/- Migration prerequisite: selected declarations from
R5Lab/AlgebraicGeometry/Curves/LocalModels/PointedResolution/CriticalCubic/Affine.lean.
Frozen R5 packet f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 7b96346da695d3620f0eaf7365062370f583852995e6c61c2bebb894bf359293.
The later pointed-resolution assembly and unused fraction-field API remain downstream. -/
