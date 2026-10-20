/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ExtensionPoints
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineField

/-!
# Nonzero affine functions have finitely many Weierstrass zeros

Source: ordinary R5 Weierstrass.CofinitePoints, lines 81–195.
The actual rank-two norm and finite x-coordinate fibres prove finiteness.
No group-law compatibility or analytic uniformization is used.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped Polynomial.Bivariate
open AlgebraicGeometry.Scheme.OverField
namespace WeierstrassCurve.Projective
universe u
variable {k K : Type u} [Field k] [Field K]

@[simp] theorem affinePointEvalExtension_polynomial (W : WeierstrassCurve k)
    (f : k →+* K) (x y : K) (h : (W.map f).toAffine.Equation x y)
    (p : Polynomial k) :
    affinePointEvalExtension W f x y h (AdjoinRoot.of W.toAffine.polynomial p) =
      Polynomial.eval₂ f x p := by
  simp [affinePointEvalExtension, AdjoinRoot.lift_of]

/-- A zero of a coordinate-ring function is a zero of its rank-two norm. -/
theorem affinePointEvalExtension_norm_eq_zero (W : WeierstrassCurve k)
    (f : k →+* K) (x y : K) (h : (W.map f).toAffine.Equation x y)
    (d : affineRing W) (hd : affinePointEvalExtension W f x y h d = 0) :
    Polynomial.eval₂ f x (Algebra.norm (Polynomial k) d) = 0 := by
  obtain ⟨p, r, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq d
  rw [← affinePointEvalExtension_polynomial W f x y h]
  change affinePointEvalExtension W f x y h
    (AdjoinRoot.of W.toAffine.polynomial
      (Algebra.norm (Polynomial k) (p • (1 : affineRing W) +
        r • WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Y))) = 0
  rw [WeierstrassCurve.Affine.CoordinateRing.coe_norm_smul_basis, map_mul, map_mul]
  have hh : WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (C p + C r * X) =
      p • (1 : affineRing W) + r • WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Y := by
    simp [WeierstrassCurve.Affine.CoordinateRing.smul, map_add, map_mul]
  rw [hh, hd, zero_mul]

/-- Actual geometric points in the affine basic open D(d). Infinity is excluded. -/
def affineBasicOpenPoints (W : WeierstrassCurve k) (f : k →+* K)
    (d : affineRing W) : Set (W.map f).toAffine.Point :=
  {P | match P with
    | .zero => False
    | .some x y h => affinePointEvalExtension W f x y h.1 d ≠ 0}

/-- A nonzero function on the literal Weierstrass affine chart has only finitely
many geometric zeros, and adjoining infinity preserves finiteness. This uses the
nonzero rank-two norm polynomial and the at-most-two-point x-coordinate fibres. -/
theorem affineBasicOpenPoints_finite_compl (W : WeierstrassCurve k) (f : k →+* K)
    (d : affineRing W) (hd : d ≠ 0) : (affineBasicOpenPoints W f d)ᶜ.Finite := by
  let N : Polynomial K := (Algebra.norm (Polynomial k) d).map f
  have hN : N ≠ 0 := by
    apply Polynomial.map_ne_zero
    exact (Algebra.norm_eq_zero_iff_of_basis
      (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)).not.mpr hd
  have hroots : {x : K | N.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hN
  have hpre : {P : (W.map f).toAffine.Point | N.IsRoot (P.xRep 0)}.Finite :=
    hroots.preimage' (fun x _ =>
      WeierstrassCurve.Affine.finite_preimage_xRep0 (W := (W.map f).toAffine) x)
  apply (hpre.union (Set.finite_singleton 0)).subset
  intro P hP
  cases P with
  | zero => exact Or.inr rfl
  | some x y h =>
      left
      change N.IsRoot x
      simp only [Polynomial.IsRoot, N, Polynomial.eval_map]
      apply affinePointEvalExtension_norm_eq_zero W f x y h.1 d
      simpa only [affineBasicOpenPoints, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using hP

/-- Every x-value occurs at an actual nonsingular point of a nonsingular
Weierstrass curve over an algebraically closed characteristic-zero field. -/
theorem point_xRep_surjective [IsAlgClosed K] [CharZero K] (W : WeierstrassCurve K)
    (hΔ : W.Δ ≠ 0) : Function.Surjective (fun P : W.toAffine.Point => P.xRep 0) := by
  intro x
  obtain ⟨y, hy⟩ := exists_affine_y W x
  exact ⟨.some x y ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hy), rfl⟩

/-- Infinitude is proved from actual x-coordinate surjectivity. -/
theorem infinite_point [IsAlgClosed K] [CharZero K] (W : WeierstrassCurve K)
    (hΔ : W.Δ ≠ 0) : Infinite W.toAffine.Point :=
  Infinite.of_surjective _ (point_xRep_surjective W hΔ)


/-- Scheme-valued version of the actual affine D(d), using the proved coordinate
bijection onto points of the original base-field curve. -/
def affineBasicOpenSchemePoints (W : WeierstrassCurve k) (f : k →+* K)
    (hΔ : W.Δ ≠ 0) (d : affineRing W) : Set (extensionPointSource f ⟶ curveOver W) :=
  (coordinateExtensionEquiv W f hΔ).symm ⁻¹' affineBasicOpenPoints W f d

theorem affineBasicOpenSchemePoints_finite_compl (W : WeierstrassCurve k)
    (f : k →+* K) (hΔ : W.Δ ≠ 0) (d : affineRing W) (hd : d ≠ 0) :
    (affineBasicOpenSchemePoints W f hΔ d)ᶜ.Finite :=
  (affineBasicOpenPoints_finite_compl W f d hd).preimage
    (coordinateExtensionEquiv W f hΔ).symm.injective.injOn

theorem infinite_extension_scheme_points [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve k) (f : k →+* K) (hΔ : W.Δ ≠ 0) :
    Infinite (extensionPointSource f ⟶ curveOver W) := by
  have hΔ' : (W.map f).Δ ≠ 0 := by simpa using f.injective.ne hΔ
  let := infinite_point (W.map f) hΔ'
  exact Infinite.of_injective _ (coordinateExtensionEquiv W f hΔ).injective




end WeierstrassCurve.Projective
