/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Scalars


/-!
# The original affine chart map and its literal generic algebra

The common generic field of an affine birational chart is its native
`Spec R` function field. The original chart homomorphism, followed by the
native R-fraction inclusion, supplies the base-ring algebra and fraction
property used to localize the original differential basis.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FunctionField

/-- On an original affine scheme map the generic scalar is the literal chart
homomorphism followed by the canonical fraction inclusion. -/
theorem genericScalar_specMap {A R : CommRingCat.{u}} [IsDomain R] (σ : A ⟶ R) :
    genericScalar (Spec.map σ) =
      σ ≫ CommRingCat.ofHom (algebraMap R (Spec R).functionField) := by
  have hη : (Spec R).fromSpecStalk (genericPoint (Spec R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Spec R).functionField)) :=
    Spec.fromSpecStalk_eq' _ _
  unfold genericScalar
  rw [hη, ← Spec.map_comp, Spec.preimage_map]

/-- The original birational chart makes its own native generic field a
fraction field of the original base through the literal composed ring map. -/
theorem specMap_generic_isFractionRing
    {A R : CommRingCat.{u}} [IsDomain A] [IsDomain R]
    (σ : A ⟶ R) [IsDominant (Spec.map σ)]
    (hσ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (Spec.map σ)))) :
    letI := ((algebraMap R (Spec R).functionField).comp σ.hom).toAlgebra
    IsFractionRing A (Spec R).functionField := by
  have h := genericScalar_isFractionRing (Spec.map σ) hσ
  rw [genericScalar_specMap] at h
  exact h

end AlgebraicGeometry.Scheme.FunctionField
