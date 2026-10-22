/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Genus.Charts
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Finite free projections of the original affine Weierstrass ring

The native quadratic basis and existing monic cubic presentation are retained.
The cubic basis is transported onto the same original affine coordinate ring,
with the coefficient variable mapped to its original y-coordinate. Its scalar
structure is an explicit local value; the native global x-algebra is unchanged.

Over a local base, use the x-projection if 2 is a unit and otherwise use the
y-projection of degree 3. The degree is already a unit in the original base
ring. The native trace, divided by that actual unit, retracts the original
coefficient map of the full finite free algebra.
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

/-- The native polynomial coefficient map whose variable is the original x-coordinate. -/
def xProjection (W : WeierstrassCurve R) : R[X] →+* affineRing W :=
  algebraMap R[X] (affineRing W)

@[simp]
lemma xProjection_X (W : WeierstrassCurve R) : xProjection W X = affineX W := rfl

@[simp]
lemma xProjection_C (W : WeierstrassCurve R) (r : R) :
    xProjection W (C r) = algebraMap R (affineRing W) r := by
  exact (IsScalarTower.algebraMap_apply R R[X] (affineRing W) r).symm

/-- The polynomial coefficient map whose variable is the same original y-coordinate. -/
def yProjection (W : WeierstrassCurve R) : R[X] →+* affineRing W :=
  (Polynomial.aeval (affineY W)).toRingHom

@[simp]
lemma yProjection_X (W : WeierstrassCurve R) : yProjection W X = affineY W := by
  change Polynomial.aeval (affineY W) X = affineY W
  exact Polynomial.aeval_X _

@[simp]
lemma yProjection_C (W : WeierstrassCurve R) (r : R) :
    yProjection W (C r) = algebraMap R (affineRing W) r := by
  change Polynomial.aeval (affineY W) (C r) = algebraMap R (affineRing W) r
  exact Polynomial.aeval_C _ _

/-- The y-scalar structure is a value, never a second global polynomial-algebra instance. -/
@[instance_reducible]
def yAlgebra (W : WeierstrassCurve R) : Algebra R[X] (affineRing W) :=
  (yProjection W).toAlgebra

/-- The existing cubic equivalence is linear over the actual original y-coefficient map. -/
def yAlgEquiv (W : WeierstrassCurve R) :
    letI : Algebra R[X] (affineRing W) := yAlgebra W
    affineCubicRing W ≃ₐ[R[X]] affineRing W := by
  letI : Algebra R[X] (affineRing W) := yAlgebra W
  refine { (affineCubicEquiv W).toRingEquiv with commutes' := ?_ }
  intro p
  change affineCubicToRing W (AdjoinRoot.of (affineCubicPolynomial W) p) =
    Polynomial.aeval (affineY W) p
  simp only [affineCubicToRing, AdjoinRoot.liftAlgHom_of]

/-- The explicit scalar transport changes no value in the existing cubic comparison. -/
@[simp]
lemma yAlgEquiv_apply (W : WeierstrassCurve R) (a : affineCubicRing W) :
    letI : Algebra R[X] (affineRing W) := yAlgebra W
    yAlgEquiv W a = affineCubicEquiv W a := rfl

/-- Finiteness and freeness over the actual y-map hold over every commutative base ring. -/
theorem yProjection_finiteFree (W : WeierstrassCurve R) :
    letI : Algebra R[X] (affineRing W) := yAlgebra W
    Module.Free R[X] (affineRing W) ∧ Module.Finite R[X] (affineRing W) := by
  let : Algebra R[X] (affineRing W) := yAlgebra W
  let b := (AdjoinRoot.powerBasis' (affineCubicPolynomial_monic W)).basis.map
    (yAlgEquiv W).toLinearEquiv
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

/-- The original affine ring has the actual basis `1,x,x²` over its y-coefficient map. -/
def yBasis [Nontrivial R] (W : WeierstrassCurve R) :
    letI : Algebra R[X] (affineRing W) := yAlgebra W
    Basis (Fin 3) R[X] (affineRing W) := by
  letI : Algebra R[X] (affineRing W) := yAlgebra W
  exact (affineCubicBasis W).map (yAlgEquiv W).toLinearEquiv

@[simp]
lemma yBasis_apply [Nontrivial R] (W : WeierstrassCurve R) (i : Fin 3) :
    letI : Algebra R[X] (affineRing W) := yAlgebra W
    yBasis W i = affineX W ^ (i : ℕ) := by
  let : Algebra R[X] (affineRing W) := yAlgebra W
  rw [yBasis, Basis.map_apply, affineCubicBasis_apply]
  change yAlgEquiv W (affineCubicX W ^ (i : ℕ)) = affineX W ^ (i : ℕ)
  rw [map_pow]
  change affineCubicToRing W (affineCubicX W) ^ (i : ℕ) = affineX W ^ (i : ℕ)
  rw [affineCubicToRing_x]

/-- The y-projection has the literal rank three when the base is nontrivial. -/
theorem yProjection_finrank [Nontrivial R] (W : WeierstrassCurve R) :
    letI : Algebra R[X] (affineRing W) := yAlgebra W
    Module.finrank R[X] (affineRing W) = 3 := by
  let : Algebra R[X] (affineRing W) := yAlgebra W
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (yBasis W)

/-- The integral projection degree uses the original base-ring unit test. -/
def projectionDegree (R : Type u) [CommRing R] : ℕ := by
  classical
  exact if IsUnit (2 : R) then 2 else 3

/-- The selected scalar structure retains the native x-algebra in the degree-two branch. -/
@[instance_reducible]
def projectionAlgebra (W : WeierstrassCurve R) : Algebra R[X] (affineRing W) := by
  classical
  exact if IsUnit (2 : R) then inferInstance else yAlgebra W

/-- A unit two selects exactly the existing native x-scalar structure. -/
lemma projectionAlgebra_of_isUnit_two (W : WeierstrassCurve R) (h : IsUnit (2 : R)) :
    projectionAlgebra W = (inferInstance : Algebra R[X] (affineRing W)) := by
  classical
  exact ite_eq_left h

/-- A nonunit two selects exactly the actual y-scalar structure. -/
lemma projectionAlgebra_of_not_isUnit_two (W : WeierstrassCurve R)
    (h : ¬ IsUnit (2 : R)) : projectionAlgebra W = yAlgebra W := by
  classical
  exact ite_eq_right h

/-- The actual chosen coefficient homomorphism on the same original affine ring. -/
def projectionMap (W : WeierstrassCurve R) : R[X] →+* affineRing W :=
  @algebraMap R[X] (affineRing W) _ _ (projectionAlgebra W)

open Classical in
/-- The selected variable is the original x-coordinate or original y-coordinate. -/
@[simp]
lemma projectionMap_X (W : WeierstrassCurve R) :
    projectionMap W X = if IsUnit (2 : R) then affineX W else affineY W := by
  by_cases h : IsUnit (2 : R)
  · rw [ite_eq_left h]
    unfold projectionMap
    rw [projectionAlgebra_of_isUnit_two W h]
  · rw [ite_eq_right h]
    unfold projectionMap
    rw [projectionAlgebra_of_not_isUnit_two W h]
    change yProjection W X = affineY W
    exact yProjection_X W

/-- Both projection branches preserve the actual original base-ring constants. -/
@[simp]
lemma projectionMap_C (W : WeierstrassCurve R) (r : R) :
    projectionMap W (C r) = algebraMap R (affineRing W) r := by
  classical
  by_cases h : IsUnit (2 : R)
  · unfold projectionMap
    rw [projectionAlgebra_of_isUnit_two W h]
    exact xProjection_C W r
  · unfold projectionMap
    rw [projectionAlgebra_of_not_isUnit_two W h]
    change yProjection W (C r) = algebraMap R (affineRing W) r
    exact yProjection_C W r

/-- The chosen finite basis is exactly the existing quadratic basis or the
transport of the existing cubic basis, according to the original unit test. -/
def projectionBasis [Nontrivial R] (W : WeierstrassCurve R) :
    letI : Algebra R[X] (affineRing W) := projectionAlgebra W
    Basis (Fin (projectionDegree R)) R[X] (affineRing W) := by
  classical
  by_cases h : IsUnit (2 : R)
  · rw [projectionAlgebra_of_isUnit_two W h]
    simpa only [projectionDegree, ite_eq_left h] using
      (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)
  · rw [projectionAlgebra_of_not_isUnit_two W h]
    simpa only [projectionDegree, ite_eq_right h] using yBasis W

/-- The full chosen original algebra is finite free over every commutative base ring. -/
theorem projection_finiteFree (W : WeierstrassCurve R) :
    letI : Algebra R[X] (affineRing W) := projectionAlgebra W
    Module.Free R[X] (affineRing W) ∧ Module.Finite R[X] (affineRing W) := by
  classical
  by_cases h : IsUnit (2 : R)
  · rw [projectionAlgebra_of_isUnit_two W h]
    exact ⟨Module.Free.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine),
      Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)⟩
  · rw [projectionAlgebra_of_not_isUnit_two W h]
    exact yProjection_finiteFree W

/-- The native module finrank is exactly the chosen integral projection degree. -/
theorem projection_finrank [Nontrivial R] (W : WeierstrassCurve R) :
    letI : Algebra R[X] (affineRing W) := projectionAlgebra W
    Module.finrank R[X] (affineRing W) = projectionDegree R := by
  let : Algebra R[X] (affineRing W) := projectionAlgebra W
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (projectionBasis W)

section LocalBase

variable [IsLocalRing R]

/-- If two is not a unit in the original local ring, three is a unit there. -/
lemma isUnit_three_of_not_isUnit_two (h2 : ¬ IsUnit (2 : R)) : IsUnit (3 : R) := by
  obtain h | h := IsLocalRing.isUnit_or_isUnit_of_add_one
    (a := (-2 : R)) (b := (3 : R)) (by ring)
  · exact False.elim (h2 ((IsUnit.neg_iff (2 : R)).mp h))
  · exact h

/-- The selected degree is a unit already in the original local base ring. -/
theorem projectionDegree_isUnit : IsUnit (projectionDegree R : R) := by
  classical
  by_cases h : IsUnit (2 : R)
  · simpa only [projectionDegree, ite_eq_left h, Nat.cast_ofNat] using h
  · simpa only [projectionDegree, ite_eq_right h, Nat.cast_ofNat] using
      isUnit_three_of_not_isUnit_two h

/-- The same degree remains a unit in the original polynomial coefficient ring. -/
theorem projectionDegree_polynomial_isUnit : IsUnit (projectionDegree R : R[X]) := by
  simpa only [map_natCast] using (projectionDegree_isUnit (R := R)).map (Polynomial.C : R →+* R[X])

/-- The actual original-ring unit used to normalize the native trace. -/
def degreeUnit : Rˣ := (projectionDegree_isUnit (R := R)).unit

@[simp]
lemma degreeUnit_val : (degreeUnit (R := R) : R) = (projectionDegree R : R) :=
  IsUnit.unit_spec _

/-- The actual polynomial-base-linear trace divided by the chosen original-ring degree unit. -/
def normalizedTrace (W : WeierstrassCurve R) :
    letI : Algebra R[X] (affineRing W) := projectionAlgebra W
    affineRing W →ₗ[R[X]] R[X] := by
  letI : Algebra R[X] (affineRing W) := projectionAlgebra W
  exact C (↑((degreeUnit (R := R))⁻¹) : R) • Algebra.trace R[X] (affineRing W)

/-- Exact trace retraction of the actual chosen coefficient map on the full algebra. -/
@[simp]
theorem normalizedTrace_projectionMap (W : WeierstrassCurve R) (p : R[X]) :
    letI : Algebra R[X] (affineRing W) := projectionAlgebra W
    normalizedTrace W (projectionMap W p) = p := by
  let : Algebra R[X] (affineRing W) := projectionAlgebra W
  change C (↑((degreeUnit (R := R))⁻¹) : R) *
    Algebra.trace R[X] (affineRing W) (algebraMap R[X] (affineRing W) p) = p
  rw [Algebra.trace_algebraMap_of_basis (projectionBasis W)]
  simp only [Fintype.card_fin, nsmul_eq_mul]
  have hu : C (degreeUnit (R := R) : R) = (projectionDegree R : R[X]) := by
    rw [degreeUnit_val]
    exact map_natCast C _
  rw [← hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-- The exact retraction identity as a composition of original polynomial-linear maps. -/
theorem normalizedTrace_comp (W : WeierstrassCurve R) :
    letI : Algebra R[X] (affineRing W) := projectionAlgebra W
    (normalizedTrace W).comp (Algebra.linearMap R[X] (affineRing W)) = LinearMap.id := by
  let : Algebra R[X] (affineRing W) := projectionAlgebra W
  apply LinearMap.ext
  intro p
  change normalizedTrace W (projectionMap W p) = p
  exact normalizedTrace_projectionMap W p

/-- The chosen original coefficient homomorphism is injective, by its actual trace retraction. -/
theorem projectionMap_injective (W : WeierstrassCurve R) :
    Function.Injective (projectionMap W) := by
  let : Algebra R[X] (affineRing W) := projectionAlgebra W
  intro p q hpq
  have h := congrArg (normalizedTrace W) hpq
  simpa only [normalizedTrace_projectionMap] using h

end LocalBase

end WeierstrassCurve.FiniteProjection
