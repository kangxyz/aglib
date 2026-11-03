/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Group.Connected
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Graded

/-!
# The original scalar augmentation of coherent cohomology

The augmentation is degree-zero projection followed by the inverse of
the actual structural scalar map. It is an algebra homomorphism and its
scalar inclusion is exactly the internal degree-zero projection. Its
degree-zero normalization is preserved by every geometric pullback,
including nonflat unit sections. A coproduct or counit identity for a
coproduct is not assumed or asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {k : Type u} [Field k] (X : FScheme k)
  [IsProper X.hom] [GeometricallyIntegral X.hom]

instance structureCohomologyAlgebraNontrivial : Nontrivial (structureCohomologyAlgebra X) :=
  Function.Injective.nontrivial
    (f := fun a : k => structureCohomologyInclusion X 0 (structureH0ScalarEquiv X a))
    (fun _ _ h => (structureH0ScalarEquiv X).injective (DirectSum.of_injective 0 h))

/-- The actual degree-zero component followed by inverse structural
constants, on the original direct sum. -/
def structureCohomologyAugmentationLinear : structureCohomologyAlgebra X →ₗ[k] k :=
  (structureH0ScalarEquiv X).symm.toLinearMap ∘ₗ structureCohomologyComponent X 0

/-- Scalar inclusion of the augmentation equals the actual internal
degree-zero projection. -/
theorem structureCohomology_proj_zero (a : structureCohomologyAlgebra X) :
    GradedAlgebra.proj (structureCohomologyGrade X) 0 a =
      structureCohomologyAugmentationLinear X a • (1 : structureCohomologyAlgebra X) := by
  have h := (structureH0ScalarEquiv X).apply_symm_apply (structureCohomologyComponent X 0 a)
  change structureCohomologyAugmentationLinear X a • structureCupUnit X =
    structureCohomologyComponent X 0 a at h
  rw [structureCohomology_proj, ← h, LinearMap.map_smul]
  rfl

@[simp]
theorem structureCohomologyAugmentationLinear_one :
    structureCohomologyAugmentationLinear X 1 = 1 := by
  apply (algebraMap k (structureCohomologyAlgebra X)).injective
  simp only [Algebra.algebraMap_eq_smul_one, one_smul]
  rw [← structureCohomology_proj_zero]
  exact (GradedRing.projZeroRingHom (structureCohomologyGrade X)).map_one

theorem structureCohomologyAugmentationLinear_mul (a b : structureCohomologyAlgebra X) :
    structureCohomologyAugmentationLinear X (a * b) =
      structureCohomologyAugmentationLinear X a * structureCohomologyAugmentationLinear X b := by
  apply (algebraMap k (structureCohomologyAlgebra X)).injective
  simp only [Algebra.algebraMap_eq_smul_one]
  rw [← structureCohomology_proj_zero]
  change GradedRing.projZeroRingHom (structureCohomologyGrade X) (a * b) = _
  rw [map_mul]
  change GradedAlgebra.proj (structureCohomologyGrade X) 0 a *
    GradedAlgebra.proj (structureCohomologyGrade X) 0 b = _
  rw [structureCohomology_proj_zero, structureCohomology_proj_zero]
  rw [smul_mul_assoc, one_mul, ← mul_smul]

/-- The canonical augmentation of the actual coherent-cohomology
algebra, with no additional theorem-family input. -/
def structureCohomologyAugmentation : structureCohomologyAlgebra X →ₐ[k] k :=
  AlgHom.ofLinearMap (structureCohomologyAugmentationLinear X)
    (structureCohomologyAugmentationLinear_one X)
    (structureCohomologyAugmentationLinear_mul X)

@[simp]
theorem structureCohomologyAugmentation_apply (a : structureCohomologyAlgebra X) :
    structureCohomologyAugmentation X a =
      (structureH0ScalarEquiv X).symm (structureCohomologyComponent X 0 a) := rfl

theorem structureCohomologyAugmentation_inclusion_zero (a : structureCohomology k X 0) :
    structureCohomologyAugmentation X (structureCohomologyInclusion X 0 a) =
      (structureH0ScalarEquiv X).symm a := by
  simp

/-- Arbitrary geometric pullback sends the actual structural scalar
class to the same scalar class, without a flatness assumption. -/
theorem structureH0ScalarEquiv_pullback {Y : FScheme k}
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] (f : X ⟶ Y) (a : k) :
    structureCohomologyPullbackLinear f 0 (structureH0ScalarEquiv Y a) =
      structureH0ScalarEquiv X a := by
  simp only [structureH0ScalarEquiv_apply, LinearMap.map_smul,
    structureCohomologyPullbackLinear_cupUnit]

/-- The inverse structural scalar comparison is compatible with every
original degree-zero geometric pullback. -/
theorem structureH0ScalarEquiv_symm_pullback {Y : FScheme k}
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] (f : X ⟶ Y)
    (a : structureCohomology k Y 0) :
    (structureH0ScalarEquiv X).symm (structureCohomologyPullbackLinear f 0 a) =
      (structureH0ScalarEquiv Y).symm a := by
  obtain ⟨b, rfl⟩ := (structureH0ScalarEquiv Y).surjective a
  rw [structureH0ScalarEquiv_pullback, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

end AlgebraicGeometry.Scheme.Cohomology
