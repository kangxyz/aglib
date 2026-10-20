/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.Coordinates
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Tactic.LinearCombination

/-!
# Admissible variable changes on the native affine coordinate algebra

Source: ordinary R5 Weierstrass.VariableChange, lines 68–246.
Mathlib owns VariableChange, its action, and Affine.CoordinateRing.
The native affine lift supplies the literal pullback; both inverse
identities and the coordinate substitution formulas are proved here.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open Polynomial
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.VariableChange
variable {R : Type u} [CommRing R]

/-- The native affine Weierstrass polynomial evaluated at the given coordinates. -/
abbrev relation (W : WeierstrassCurve R) (x y : R) : R :=
  W.toAffine.polynomial.evalEval x y

def changeX (v : WeierstrassCurve.VariableChange R) (x : R) : R :=
  (v.u : R) ^ 2 * x + v.r

def changeY (v : WeierstrassCurve.VariableChange R) (x y : R) : R :=
  (v.u : R) ^ 3 * y + v.s * (v.u : R) ^ 2 * x + v.t

lemma relation_change (W : WeierstrassCurve R) (v : WeierstrassCurve.VariableChange R)
    (x y : R) : relation W (changeX v x) (changeY v x y) =
      (v.u : R) ^ 6 * relation (v • W) x y := by
  have h (n : ℕ) : (v.u : R) ^ n * (↑v.u⁻¹ : R) ^ n = 1 :=
    pow_mul_pow_eq_one n v.u.mul_inv
  have h1 : (v.u : R) ^ 6 * (↑v.u⁻¹ : R) = (v.u : R) ^ 5 := by
    linear_combination (v.u : R) ^ 5 * h 1
  have h2 : (v.u : R) ^ 6 * (↑v.u⁻¹ : R) ^ 2 = (v.u : R) ^ 4 := by
    linear_combination (v.u : R) ^ 4 * h 2
  have h3 : (v.u : R) ^ 6 * (↑v.u⁻¹ : R) ^ 3 = (v.u : R) ^ 3 := by
    linear_combination (v.u : R) ^ 3 * h 3
  have h4 : (v.u : R) ^ 6 * (↑v.u⁻¹ : R) ^ 4 = (v.u : R) ^ 2 := by
    linear_combination (v.u : R) ^ 2 * h 4
  have h6 := h 6
  simp only [relation, WeierstrassCurve.Affine.evalEval_polynomial]
  dsimp only [changeX, changeY]
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆]
  linear_combination -(W.a₁ + 2 * v.s) * x * y * h1 +
    (W.a₂ - v.s * W.a₁ + 3 * v.r - v.s ^ 2) * x ^ 2 * h2 -
    (W.a₃ + v.r * W.a₁ + 2 * v.t) * y * h3 +
    (W.a₄ - v.s * W.a₃ + 2 * v.r * W.a₂ - (v.t + v.r * v.s) * W.a₁ +
      3 * v.r ^ 2 - 2 * v.s * v.t) * x * h4 +
    (W.a₆ + v.r * W.a₄ + v.r ^ 2 * W.a₂ + v.r ^ 3 - v.t * W.a₃ - v.t ^ 2 -
      v.r * v.t * W.a₁) * h6

private lemma affine_relation_eval (W : WeierstrassCurve R) :
    relation (W.map (algebraMap R W.toAffine.CoordinateRing)) (affineX W) (affineY W) = 0 := by
  simpa only [relation, WeierstrassCurve.Affine.evalEval_polynomial,
    WeierstrassCurve.map] using WeierstrassCurve.affine_relation W

end WeierstrassCurve.VariableChange

namespace WeierstrassCurve.VariableChange
variable {R : Type u} [CommRing R]

lemma changeX_inv (v : WeierstrassCurve.VariableChange R) (x : R) :
    changeX v⁻¹ (changeX v x) = x := by
  have h2 := pow_mul_pow_eq_one 2 v.u.inv_mul
  dsimp only [changeX, WeierstrassCurve.VariableChange.inv_def]
  linear_combination x * h2

lemma changeY_inv (v : WeierstrassCurve.VariableChange R) (x y : R) :
    changeY v⁻¹ (changeX v x) (changeY v x y) = y := by
  have h3 := pow_mul_pow_eq_one 3 v.u.inv_mul
  dsimp only [changeX, changeY, WeierstrassCurve.VariableChange.inv_def]
  linear_combination y * h3

lemma changeX_inv' (v : WeierstrassCurve.VariableChange R) (x : R) :
    changeX v (changeX v⁻¹ x) = x := by
  simpa only [inv_inv] using changeX_inv v⁻¹ x

lemma changeY_inv' (v : WeierstrassCurve.VariableChange R) (x y : R) :
    changeY v (changeX v⁻¹ x) (changeY v⁻¹ x y) = y := by
  simpa only [inv_inv] using changeY_inv v⁻¹ x y

variable {S : Type*} [CommRing S]

lemma changeX_map (v : WeierstrassCurve.VariableChange R) (x : R) (f : R →+* S) :
    f (changeX v x) = changeX (v.map f) (f x) := by
  simp [changeX, WeierstrassCurve.VariableChange.map]
lemma changeY_map (v : WeierstrassCurve.VariableChange R) (x y : R) (f : R →+* S) :
    f (changeY v x y) = changeY (v.map f) (f x) (f y) := by
  simp [changeY, WeierstrassCurve.VariableChange.map]

lemma map_inv (v : WeierstrassCurve.VariableChange R) (f : R →+* S) :
    (v⁻¹).map f = (v.map f)⁻¹ := by
  exact (WeierstrassCurve.VariableChange.mapHom f).map_inv v

/-- The actual pullback on affine coordinate rings of an admissible change. -/
def affineMap (W : WeierstrassCurve R) (v : WeierstrassCurve.VariableChange R) :
    W.toAffine.CoordinateRing →ₐ[R] (v • W).toAffine.CoordinateRing :=
  WeierstrassCurve.affineLift W
    (changeX (v.map (algebraMap R _)) (affineX (v • W)))
    (changeY (v.map (algebraMap R _)) (affineX (v • W)) (affineY (v • W))) (by
      have h : relation (W.map (algebraMap R (v • W).toAffine.CoordinateRing))
          (changeX (v.map (algebraMap R _)) (affineX (v • W)))
          (changeY (v.map (algebraMap R _)) (affineX (v • W)) (affineY (v • W))) = 0 := by
        rw [relation_change, WeierstrassCurve.map_variableChange, affine_relation_eval, mul_zero]
      simpa only [relation, WeierstrassCurve.Affine.evalEval_polynomial,
        WeierstrassCurve.map] using h)

@[simp] lemma affineMap_x (W : WeierstrassCurve R) (v : WeierstrassCurve.VariableChange R) :
    affineMap W v (affineX W) =
      changeX (v.map (algebraMap R _)) (affineX (v • W)) := affineLift_x _ _ _ _
@[simp] lemma affineMap_y (W : WeierstrassCurve R) (v : WeierstrassCurve.VariableChange R) :
    affineMap W v (affineY W) =
      changeY (v.map (algebraMap R _)) (affineX (v • W)) (affineY (v • W)) :=
  affineLift_y _ _ _ _

/-- The actual inverse pullback, using the inverse admissible substitution. -/
def affineInverse (W : WeierstrassCurve R) (v : WeierstrassCurve.VariableChange R) :
    (v • W).toAffine.CoordinateRing →ₐ[R] W.toAffine.CoordinateRing :=
  WeierstrassCurve.affineLift (v • W)
    (changeX ((v.map (algebraMap R _))⁻¹) (affineX W))
    (changeY ((v.map (algebraMap R _))⁻¹) (affineX W) (affineY W)) (by
      have h : relation ((v • W).map (algebraMap R W.toAffine.CoordinateRing))
          (changeX ((v.map (algebraMap R _))⁻¹) (affineX W))
          (changeY ((v.map (algebraMap R _))⁻¹) (affineX W) (affineY W)) = 0 := by
        rw [relation_change, ← WeierstrassCurve.map_variableChange,
          inv_smul_smul, affine_relation_eval, mul_zero]
      simpa only [relation, WeierstrassCurve.Affine.evalEval_polynomial,
        WeierstrassCurve.map] using h)

@[simp] lemma affineInverse_x (W : WeierstrassCurve R) (v : WeierstrassCurve.VariableChange R) :
    affineInverse W v (affineX (v • W)) =
      changeX ((v.map (algebraMap R _))⁻¹) (affineX W) := affineLift_x _ _ _ _
@[simp] lemma affineInverse_y (W : WeierstrassCurve R) (v : WeierstrassCurve.VariableChange R) :
    affineInverse W v (affineY (v • W)) =
      changeY ((v.map (algebraMap R _))⁻¹) (affineX W) (affineY W) :=
  affineLift_y _ _ _ _

lemma algHom_changeX {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (v : WeierstrassCurve.VariableChange R) (x : A) :
    f (changeX (v.map (algebraMap R A)) x) =
      changeX (v.map (algebraMap R B)) (f x) := by
  simp [changeX, WeierstrassCurve.VariableChange.map]
lemma algHom_changeY {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (v : WeierstrassCurve.VariableChange R) (x y : A) :
    f (changeY (v.map (algebraMap R A)) x y) =
      changeY (v.map (algebraMap R B)) (f x) (f y) := by
  simp [changeY, WeierstrassCurve.VariableChange.map]

/-- Literal affine Weierstrass coordinate rings are isomorphic under the
admissible substitution; both inverse identities are proved on X and Y. -/
def affineEquiv (W : WeierstrassCurve R) (v : WeierstrassCurve.VariableChange R) :
    W.toAffine.CoordinateRing ≃ₐ[R] (v • W).toAffine.CoordinateRing :=
  AlgEquiv.ofAlgHom (affineMap W v) (affineInverse W v)
    (by
      apply affine_ext
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, affineInverse_x]
        rw [← map_inv, algHom_changeX, affineMap_x, map_inv, changeX_inv]
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, affineInverse_y]
        rw [← map_inv, algHom_changeY, affineMap_x, affineMap_y, map_inv, changeY_inv])
    (by
      apply affine_ext
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, affineMap_x,
          algHom_changeX, affineInverse_x, changeX_inv']
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, affineMap_y,
          algHom_changeY, affineInverse_x, affineInverse_y, changeY_inv'])


end WeierstrassCurve.VariableChange
