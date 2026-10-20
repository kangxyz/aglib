/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineChart
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Rank-two affine injectivity and existence of coordinates

Source: ordinary R5 Weierstrass.Points, lines 605–640.
The norm argument preserves the actual x-polynomial subalgebra.
The quadratic existence result retains algebraic closedness and characteristic zero.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Projective
universe u v
variable {k : Type u} [Field k] {L : Type v} [Field L]

/-- For the actual rank-two Weierstrass coordinate algebra, injectivity on the
x-polynomial subalgebra implies injectivity on the whole affine ring. The proof
uses its constructed rank-two norm and conjugation, not a curve-specific premise. -/
theorem affineRingHom_injective (W : WeierstrassCurve k) (g : affineRing W →+* L)
    (hx : Function.Injective (g.comp (algebraMap (Polynomial k) (affineRing W)))) :
    Function.Injective g := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨p, r, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  apply (Algebra.norm_eq_zero_iff_of_basis
    (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)).mp
  apply hx
  rw [RingHom.comp_apply, RingHom.comp_apply, map_zero, map_zero]
  change g (AdjoinRoot.of W.toAffine.polynomial
    (Algebra.norm (Polynomial k) (p • (1 : affineRing W) +
      r • WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Y))) = 0
  rw [WeierstrassCurve.Affine.CoordinateRing.coe_norm_smul_basis]
  rw [map_mul, map_mul]
  have hh : WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (C p + C r * X) =
      p • (1 : affineRing W) + r • WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Y := by
    simp [WeierstrassCurve.Affine.CoordinateRing.smul, map_add, map_mul]
  rw [hh, ha, zero_mul]

/-- Each x-coordinate occurs on an affine Weierstrass curve over an explicitly
algebraically closed field. This is an ordinary quadratic polynomial argument. -/
theorem exists_affine_y [IsAlgClosed L] [CharZero L] (W : WeierstrassCurve L) (x : L) :
    ∃ y : L, W.toAffine.Equation x y := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
    ((W.a₁ * x + W.a₃) ^ 2 + 4 * (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
    (show 0 < 2 by omega)
  refine ⟨(z - (W.a₁ * x + W.a₃)) / 2,
    (WeierstrassCurve.Affine.equation_iff' _ _).mpr ?_⟩
  change ((z - (W.a₁ * x + W.a₃)) / 2) ^ 2 +
      W.a₁ * x * ((z - (W.a₁ * x + W.a₃)) / 2) +
      W.a₃ * ((z - (W.a₁ * x + W.a₃)) / 2) -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0
  linear_combination hz / 4


end WeierstrassCurve.Projective
