/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointedTargetRestriction
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # An original pointed étale test on a standard-smooth affine curve

The affine chart is standard smooth over the unchanged original coefficient
base, with its actual structural equation and original geometric mark.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
universe u

/-- Refine an original étale test at a given field point by a standard-smooth
curve chart over the original ring, with the same point and structural map. -/
theorem exists_standardSmooth_affine_pointed_test
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 A C]
    (U : (Spec (.of C)).Etale) (Ω : Type u) [Field Ω]
    (ξ : Spec (.of Ω) ⟶ U.left) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Algebra.IsStandardSmoothOfRelativeDimension 1 A D ∧
      ∃ (j : Spec (.of D) ⟶ U.left) (z : Spec (.of Ω) ⟶ Spec (.of D)),
        IsOpenImmersion j ∧ z ≫ j = ξ ∧
          (j ≫ U.hom) ≫ Spec.algebraMap A C = Spec.algebraMap A D := by
  obtain ⟨D, hD, hDΩ, j, hj, hξ⟩ := exists_affineSpec_chart_of_fieldPoint Ω ξ
  let := hD
  let := hDΩ
  let := hj
  let v : Spec (.of D) ⟶ Spec (.of C) := j ≫ U.hom
  let : Algebra C D := (Spec.preimage v).hom.toAlgebra
  have hv : Spec.algebraMap C D = v := Spec.map_preimage v
  let : Algebra A D := Algebra.compHom D (algebraMap A C)
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale C D := by
    have he : Etale (Spec.algebraMap C D) := by
      rw [hv]
      infer_instance
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale)
        (φ := CommRingCat.ofHom (algebraMap C D))).mp he)
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 C D :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  have hsm : Algebra.IsStandardSmoothOfRelativeDimension 1 A D :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans (m := 0) (n := 1) A C D
  refine ⟨D, hD, inferInstance, hsm, j, Spec.algebraMap D Ω, hj, hξ, ?_⟩
  change v ≫ Spec.algebraMap A C = Spec.algebraMap A D
  rw [← hv, ← Spec.map_comp]
  rfl

end AlgebraicGeometry.Scheme
