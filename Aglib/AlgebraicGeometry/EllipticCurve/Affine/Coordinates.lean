/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Tactic.LinearCombination

/-!
# Actual coordinates and universal maps of affine Weierstrass curves

The carrier is literally Mathlib's `W.toAffine.CoordinateRing`. The original
coordinate elements, relation and algebra maps use that same carrier.
Source slices: `Curves/Nodal/SplitChart`, affine coordinate/lift/ext declarations,
and `Curves/Nodal/CriticalPoint`, scale-one translation and coefficient formulas.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SplitChart SHA-256:
`cbe0ba17c6043949ad0cda88aa7cfb298eb19a8d8f70adc0f00f4eefd62e8927`.
CriticalPoint SHA-256:
`20b260971e41f5b97a10a66e9f1cb81b0ca19b5c26fe50866af904cead72162c`.
No critical-lift, Henselian or tangent-chart construction is imported here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
open scoped Polynomial.Bivariate
universe u
namespace WeierstrassCurve
variable {R : Type u} [CommRing R]

/-- The `x` coordinate in the affine Weierstrass coordinate ring. -/
abbrev affineX (W : WeierstrassCurve R) : W.toAffine.CoordinateRing := algebraMap R[X] _ X
/-- The `y` coordinate in the affine Weierstrass coordinate ring. -/
abbrev affineY (W : WeierstrassCurve R) : W.toAffine.CoordinateRing :=
  AdjoinRoot.root W.toAffine.polynomial

lemma affine_relation (W : WeierstrassCurve R) :
    affineY W ^ 2 + algebraMap R _ W.a₁ * affineX W * affineY W +
      algebraMap R _ W.a₃ * affineY W -
    (affineX W ^ 3 + algebraMap R _ W.a₂ * affineX W ^ 2 +
      algebraMap R _ W.a₄ * affineX W + algebraMap R _ W.a₆) = 0 := by
  have h := AdjoinRoot.eval₂_root W.toAffine.polynomial
  change (Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y -
    C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)).eval₂
      (algebraMap R[X] (W.toAffine.CoordinateRing)) (affineY W) = 0 at h
  simp only [ eval₂_sub, eval₂_add, eval₂_mul,
    eval₂_pow, eval₂_X, eval₂_C, map_add, map_mul, map_pow] at h
  simpa only [← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply R R[X],
    ← Polynomial.algebraMap_eq, add_mul, add_assoc] using h

variable {S : Type*} [CommRing S] [Algebra R S]

/-- The algebra map from the affine Weierstrass coordinate ring determined by coordinates `x`
and `y` satisfying the Weierstrass equation. -/
def affineLift (W : WeierstrassCurve R) (x y : S)
    (h : y ^ 2 + algebraMap R S W.a₁ * x * y + algebraMap R S W.a₃ * y -
      (x ^ 3 + algebraMap R S W.a₂ * x ^ 2 + algebraMap R S W.a₄ * x +
        algebraMap R S W.a₆) = 0) : W.toAffine.CoordinateRing →ₐ[R] S :=
  AdjoinRoot.liftAlgHom W.toAffine.polynomial (aeval x) y (by
    simpa only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add,
      eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, map_add, map_mul, map_pow, AlgHom.coe_toRingHom,
      aeval_C, aeval_X, add_mul, add_assoc] using h)

@[simp] lemma affineLift_x (W : WeierstrassCurve R) (x y : S) (h) :
    affineLift W x y h (affineX W) = x := by
  simp [affineLift, affineX, AdjoinRoot.algebraMap_eq]
@[simp] lemma affineLift_y (W : WeierstrassCurve R) (x y : S) (h) :
    affineLift W x y h (affineY W) = y := by simp [affineLift, affineY]

@[ext] lemma affine_ext (W : WeierstrassCurve R) (f g : W.toAffine.CoordinateRing →ₐ[R] S)
    (hx : f (affineX W) = g (affineX W)) (hy : f (affineY W) = g (affineY W)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    exact hx
  · exact hy


/-- The actual admissible Weierstrass translation, of scale one. -/
def translate (W : WeierstrassCurve R) (r t : R) : WeierstrassCurve R :=
  WeierstrassCurve.VariableChange.mk 1 r 0 t • W

@[simp] theorem translate_a1 (W : WeierstrassCurve R) (r t : R) :
    (translate W r t).a₁ = W.a₁ := by
  simp [translate, WeierstrassCurve.variableChange_a₁]

@[simp] theorem translate_a2 (W : WeierstrassCurve R) (r t : R) :
    (translate W r t).a₂ = W.a₂ + 3 * r := by
  simp [translate, WeierstrassCurve.variableChange_a₂]

@[simp] theorem translate_a3 (W : WeierstrassCurve R) (r t : R) :
    (translate W r t).a₃ = 2 * t + W.a₁ * r + W.a₃ := by
  simp [translate, WeierstrassCurve.variableChange_a₃]
  ring

@[simp] theorem translate_a4 (W : WeierstrassCurve R) (r t : R) :
    (translate W r t).a₄ = -(W.a₁ * t - (3 * r ^ 2 + 2 * W.a₂ * r + W.a₄)) := by
  simp [translate, WeierstrassCurve.variableChange_a₄]
  ring

@[simp] theorem translate_a6 (W : WeierstrassCurve R) (r t : R) :
    (translate W r t).a₆ = -W.toAffine.polynomial.evalEval r t := by
  simp [translate, WeierstrassCurve.variableChange_a₆,
    WeierstrassCurve.Affine.evalEval_polynomial]
  ring

@[simp] theorem translate_b2 (W : WeierstrassCurve R) (r t : R) :
    (translate W r t).b₂ = W.b₂ + 12 * r := by
  simp [translate, WeierstrassCurve.variableChange_b₂]

@[simp] theorem translate_discriminant (W : WeierstrassCurve R) (r t : R) :
    (translate W r t).Δ = W.Δ := by
  simp [translate, WeierstrassCurve.variableChange_Δ]


end WeierstrassCurve
