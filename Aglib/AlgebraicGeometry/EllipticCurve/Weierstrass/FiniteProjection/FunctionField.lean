/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.FiniteProjection
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Trace.Basic

/-!
# The actual finite separable fraction-field projection

The selected polynomial projection of the original affine Weierstrass ring
induces a map between its actual native fraction fields. The commuting scalar
maps transfer the original finite-free rank to this field extension. Over a
local domain, its degree is a unit already in the original base ring, so the
field trace of one is nonzero and the extension is separable.

All scalar structures differing from the native x-structure are explicit local
values. No fraction field or coordinate ring is replaced.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Module
open WeierstrassCurve.Projective

namespace WeierstrassCurve.FiniteProjection

universe u

variable {R : Type u} [CommRing R]

/-- The original polynomial projection followed by the native fraction-ring map. -/
@[instance_reducible]
def coefficientFractionAlgebra (W : WeierstrassCurve R) :
    Algebra R[X] (FractionRing (affineRing W)) := by
  letI : Algebra R[X] (affineRing W) := projectionAlgebra W
  infer_instance

/-- The original selected projection commutes with the native target localization. -/
theorem coefficientFraction_isScalarTower (W : WeierstrassCurve R) :
    @IsScalarTower R[X] (affineRing W) (FractionRing (affineRing W))
      (projectionAlgebra W).toSMul
      (inferInstance : Algebra (affineRing W) (FractionRing (affineRing W))).toSMul
      (coefficientFractionAlgebra W).toSMul := by
  let : Algebra R[X] (affineRing W) := projectionAlgebra W
  let : Algebra R[X] (FractionRing (affineRing W)) := coefficientFractionAlgebra W
  refine IsScalarTower.of_algebraMap_eq
    (R := R[X]) (S := affineRing W) (A := FractionRing (affineRing W)) ?_
  intro p
  rfl

/-- The same integral unit degree remains a unit in the actual source fraction field. -/
theorem projectionDegree_fraction_isUnit [IsLocalRing R] :
    IsUnit (projectionDegree R : FractionRing (R[X])) := by
  simpa only [map_natCast] using
    (projectionDegree_polynomial_isUnit (R := R)).map
      (algebraMap R[X] (FractionRing (R[X])))

section LocalDomain

variable [IsDomain R] [IsLocalRing R]

/-- The actual fraction-field homomorphism induced by the original selected projection. -/
def fractionMap (W : WeierstrassCurve R) :
    FractionRing (R[X]) →+* FractionRing (affineRing W) :=
  IsFractionRing.lift (K := FractionRing (R[X]))
    (g := (algebraMap (affineRing W) (FractionRing (affineRing W))).comp (projectionMap W))
    ((IsFractionRing.injective (affineRing W) (FractionRing (affineRing W))).comp
      (projectionMap_injective W))

/-- The induced field map sends every original polynomial to its original projected value. -/
@[simp]
theorem fractionMap_algebraMap (W : WeierstrassCurve R) (p : R[X]) :
    fractionMap W (algebraMap R[X] (FractionRing (R[X])) p) =
      algebraMap (affineRing W) (FractionRing (affineRing W)) (projectionMap W p) := by
  exact IsFractionRing.lift_algebraMap _ p

/-- The induced field map is an embedding of the actual native fraction field. -/
theorem fractionMap_injective (W : WeierstrassCurve R) :
    Function.Injective (fractionMap W) :=
  (fractionMap W).injective

/-- The field map retains the numerator and denominator of every original polynomial fraction. -/
theorem fractionMap_div (W : WeierstrassCurve R) (p q : R[X]) :
    fractionMap W (algebraMap R[X] (FractionRing (R[X])) p /
      algebraMap R[X] (FractionRing (R[X])) q) =
    algebraMap (affineRing W) (FractionRing (affineRing W)) (projectionMap W p) /
      algebraMap (affineRing W) (FractionRing (affineRing W)) (projectionMap W q) := by
  rw [map_div₀, fractionMap_algebraMap, fractionMap_algebraMap]

open Classical in
/-- The selected transcendental variable remains the original x- or y-coordinate in the field. -/
theorem fractionMap_X (W : WeierstrassCurve R) :
    fractionMap W (algebraMap R[X] (FractionRing (R[X])) X) =
      if IsUnit (2 : R) then
        algebraMap (affineRing W) (FractionRing (affineRing W)) (affineX W)
      else algebraMap (affineRing W) (FractionRing (affineRing W)) (affineY W) := by
  by_cases h : IsUnit (2 : R)
  · simp only [fractionMap_algebraMap, projectionMap_X, ite_eq_left h]
  · simp only [fractionMap_algebraMap, projectionMap_X, ite_eq_right h]

/-- The induced field map preserves the same original base-ring constants. -/
theorem fractionMap_C (W : WeierstrassCurve R) (r : R) :
    fractionMap W (algebraMap R[X] (FractionRing (R[X])) (C r)) =
      algebraMap R (FractionRing (affineRing W)) r := by
  rw [fractionMap_algebraMap, projectionMap_C]
  exact (IsScalarTower.algebraMap_apply R (affineRing W)
    (FractionRing (affineRing W)) r).symm

/-- The field scalar structure is an explicit value attached to this same fraction map. -/
@[instance_reducible]
def fractionAlgebra (W : WeierstrassCurve R) :
    Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) :=
  (fractionMap W).toAlgebra

/-- The native source localization and actual induced field map form the same scalar triangle. -/
theorem fraction_isScalarTower (W : WeierstrassCurve R) :
    @IsScalarTower R[X] (FractionRing (R[X])) (FractionRing (affineRing W))
      (inferInstance : Algebra R[X] (FractionRing (R[X]))).toSMul
      (fractionAlgebra W).toSMul (coefficientFractionAlgebra W).toSMul := by
  let : Algebra R[X] (affineRing W) := projectionAlgebra W
  let : Algebra R[X] (FractionRing (affineRing W)) := coefficientFractionAlgebra W
  let : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
  refine IsScalarTower.of_algebraMap_eq
    (R := R[X]) (S := FractionRing (R[X])) (A := FractionRing (affineRing W)) ?_
  intro p
  change algebraMap (affineRing W) (FractionRing (affineRing W)) (projectionMap W p) =
    fractionMap W (algebraMap R[X] (FractionRing (R[X])) p)
  exact (fractionMap_algebraMap W p).symm

/-- The original finite-free rank is the exact degree of the actual fraction-field extension. -/
theorem fraction_finrank (W : WeierstrassCurve R) :
    letI : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
    Module.finrank (FractionRing (R[X])) (FractionRing (affineRing W)) = projectionDegree R := by
  let : Algebra R[X] (affineRing W) := projectionAlgebra W
  let : Algebra R[X] (FractionRing (affineRing W)) := coefficientFractionAlgebra W
  let : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
  let : @IsScalarTower R[X] (affineRing W) (FractionRing (affineRing W))
      (projectionAlgebra W).toSMul
      (inferInstance : Algebra (affineRing W) (FractionRing (affineRing W))).toSMul
      (coefficientFractionAlgebra W).toSMul := coefficientFraction_isScalarTower W
  let : @IsScalarTower R[X] (FractionRing (R[X])) (FractionRing (affineRing W))
      (inferInstance : Algebra R[X] (FractionRing (R[X]))).toSMul
      (fractionAlgebra W).toSMul (coefficientFractionAlgebra W).toSMul :=
    fraction_isScalarTower W
  exact (IsFractionRing.finrank_eq R[X] (FractionRing (R[X]))
    (affineRing W) (FractionRing (affineRing W))).trans (projection_finrank W)

/-- The actual extension of native fraction fields is finite-dimensional. -/
theorem fraction_finiteDimensional (W : WeierstrassCurve R) :
    letI : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
    FiniteDimensional (FractionRing (R[X])) (FractionRing (affineRing W)) := by
  let : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
  apply Module.finite_of_finrank_pos
  rw [fraction_finrank W]
  classical
  unfold projectionDegree
  split_ifs <;> decide

/-- The field trace of one is the actual selected degree, in the original fraction field. -/
@[simp]
theorem fraction_trace_one (W : WeierstrassCurve R) :
    letI : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
    Algebra.trace (FractionRing (R[X])) (FractionRing (affineRing W)) 1 =
      (projectionDegree R : FractionRing (R[X])) := by
  let : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
  simpa only [map_one, fraction_finrank W, nsmul_eq_mul, mul_one] using
    (Algebra.trace_algebraMap (R := FractionRing (R[X]))
      (S := FractionRing (affineRing W)) (1 : FractionRing (R[X])))

/-- The actual field trace is nonzero at one because the degree was a unit before localization. -/
theorem fraction_trace_one_ne_zero (W : WeierstrassCurve R) :
    letI : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
    Algebra.trace (FractionRing (R[X])) (FractionRing (affineRing W)) 1 ≠ 0 := by
  let : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
  rw [fraction_trace_one W]
  exact (projectionDegree_fraction_isUnit (R := R)).ne_zero

/-- The extension induced by the actual original polynomial projection is separable. -/
theorem fraction_isSeparable (W : WeierstrassCurve R) :
    letI : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
    Algebra.IsSeparable (FractionRing (R[X])) (FractionRing (affineRing W)) := by
  let : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
  by_contra h
  have hz := Algebra.trace_eq_zero_of_not_isSeparable h
  have he := congrArg
    (fun f : FractionRing (affineRing W) →ₗ[FractionRing (R[X])] FractionRing (R[X]) => f 1) hz
  exact fraction_trace_one_ne_zero W (by simpa only [LinearMap.zero_apply] using he)

/-- The same native fraction map gives a finite separable extension of the exact selected degree. -/
theorem fraction_extension (W : WeierstrassCurve R) :
    letI : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
    FiniteDimensional (FractionRing (R[X])) (FractionRing (affineRing W)) ∧
      Module.finrank (FractionRing (R[X])) (FractionRing (affineRing W)) = projectionDegree R ∧
      Algebra.IsSeparable (FractionRing (R[X])) (FractionRing (affineRing W)) := by
  let : Algebra (FractionRing (R[X])) (FractionRing (affineRing W)) := fractionAlgebra W
  exact ⟨fraction_finiteDimensional W, fraction_finrank W, fraction_isSeparable W⟩

end LocalDomain

end WeierstrassCurve.FiniteProjection
