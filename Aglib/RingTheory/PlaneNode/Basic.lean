/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.Algebra.Polynomial.Bivariate

/-!
# The literal plane-node algebra and its coordinate maps

`Ring c` is the actual `AdjoinRoot` presentation of R[U,V]/(UV-c).
The universal algebra map and branch-unit scaling retain their original
coordinate formulas over arbitrary commutative rings.
Source: bounded node-ring/lift/ext and unit-scale slices of
`R5Lab.AlgebraicGeometry.Curves.Nodal.SplitChart`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`cbe0ba17c6043949ad0cda88aa7cfb298eb19a8d8f70adc0f00f4eefd62e8927`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
open scoped Polynomial.Bivariate
universe u
namespace PlaneNode
variable {R : Type u} [CommRing R]
variable {S : Type*} [CommRing S] [Algebra R S]

/-- The literal node coordinate ring R[U,V]/(UV-c), presented as an AdjoinRoot. -/
def poly (c : R) : R[X][Y] := C X * Y - C (C c)
abbrev Ring (c : R) := AdjoinRoot (poly c)
abbrev U (c : R) : Ring c := algebraMap R[X] _ X
abbrev V (c : R) : Ring c := AdjoinRoot.root (poly c)
lemma relation (c : R) : U c * V c = algebraMap R _ c := by
  have h := AdjoinRoot.eval₂_root (poly c)
  change (C X * Y - C (C c)).eval₂ (algebraMap R[X] (Ring c)) (V c) = 0 at h
  simp only [ eval₂_sub, eval₂_mul, eval₂_X, eval₂_C] at h
  simpa only [← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply R R[X],
    ← Polynomial.algebraMap_eq, sub_eq_zero] using h

def lift (c : R) (x y : S) (h : x * y = algebraMap R S c) : Ring c →ₐ[R] S :=
  AdjoinRoot.liftAlgHom (poly c) (aeval x) y (by simp [poly, h])
@[simp] lemma lift_U (c : R) (x y : S) (h) :
    lift c x y h (U c) = x := by simp [lift, U, AdjoinRoot.algebraMap_eq]
@[simp] lemma lift_V (c : R) (x y : S) (h) :
    lift c x y h (V c) = y := by simp [lift, V]
@[ext] lemma hom_ext (c : R) (f g : Ring c →ₐ[R] S)
    (hx : f (U c) = g (U c)) (hy : f (V c) = g (V c)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext; exact hx
  · exact hy


def scaleHom (c : R) (a : Rˣ) : Ring ((a : R) * c) →ₐ[R] Ring c :=
  lift _ (algebraMap R _ (a : R) * U c) (V c) (by
    rw [mul_assoc, relation, ← map_mul])

@[simp] theorem scaleHom_U (c : R) (a : Rˣ) :
    scaleHom c a (U ((a : R) * c)) = algebraMap R _ (a : R) * U c := by
  simp [scaleHom]
@[simp] theorem scaleHom_V (c : R) (a : Rˣ) :
    scaleHom c a (V ((a : R) * c)) = V c := by simp [scaleHom]

def unscaleHom (c : R) (a : Rˣ) : Ring c →ₐ[R] Ring ((a : R) * c) :=
  lift _ (algebraMap R _ (↑a⁻¹ : R) * U ((a : R) * c))
    (V ((a : R) * c)) (by
      rw [mul_assoc, relation, ← map_mul]
      simp)

@[simp] theorem unscaleHom_U (c : R) (a : Rˣ) :
    unscaleHom c a (U c) =
      algebraMap R _ (↑a⁻¹ : R) * U ((a : R) * c) := by simp [unscaleHom]
@[simp] theorem unscaleHom_V (c : R) (a : Rˣ) :
    unscaleHom c a (V c) = V ((a : R) * c) := by simp [unscaleHom]

/-- Scaling one actual branch coordinate removes an arbitrary unit factor. -/
def unitScale (c : R) (a : Rˣ) : Ring ((a : R) * c) ≃ₐ[R] Ring c :=
  AlgEquiv.ofAlgHom (scaleHom c a) (unscaleHom c a)
    (by
      apply hom_ext <;> simp only [AlgHom.comp_apply, AlgHom.id_apply, scaleHom_U,
        scaleHom_V, unscaleHom_U, unscaleHom_V, map_mul, AlgHom.commutes]
      simp [← mul_assoc, ← map_mul])
    (by
      apply hom_ext <;> simp only [AlgHom.comp_apply, AlgHom.id_apply, scaleHom_U,
        scaleHom_V, unscaleHom_U, unscaleHom_V, map_mul, AlgHom.commutes]
      simp [← mul_assoc, ← map_mul])


end PlaneNode
