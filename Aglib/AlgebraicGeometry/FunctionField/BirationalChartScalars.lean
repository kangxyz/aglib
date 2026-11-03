/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Aglib.AlgebraicGeometry.FunctionField.AffineScalars
public import Aglib.AlgebraicGeometry.FunctionField.Scalars


/-!
# The original model determines the affine chart's common fraction field

For a birational model and an actual nonempty affine chart, the original
chart coefficient map followed by its own native generic inclusion is a
fraction-ring structure for the original base. The open chart's actual field
isomorphism and the model's original field isomorphism prove this property;
it is not supplied as a separate common-field certificate.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FunctionField

/-- The original model and affine chart derive the common fraction field
through the literal `Spec.preimage (j ≫ β)` coefficient map. -/
theorem modelChart_generic_isFractionRing
    {X : Scheme.{u}} [IsIntegral X] {A R : CommRingCat.{u}}
    [IsDomain A] [IsDomain R]
    (β : X ⟶ Spec A) [IsDominant β]
    (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))
    (j : Spec R ⟶ X) [IsOpenImmersion j] :
    letI := ((algebraMap R (Spec R).functionField).comp
      (Spec.preimage (j ≫ β)).hom).toAlgebra
    IsFractionRing A (Spec R).functionField := by
  let : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap j)) :=
    FunctionField.fieldMap_isIso j
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)) := hβ
  have hcomp : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (j ≫ β))) := by
    rw [Scheme.functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  have hscalar : genericScalar (j ≫ β) = Spec.preimage (j ≫ β) ≫
      CommRingCat.ofHom (algebraMap R (Spec R).functionField) :=
    (congrArg (fun k : Spec R ⟶ Spec A => genericScalar k)
      (Spec.map_preimage (j ≫ β)).symm).trans (genericScalar_specMap _)
  have h := genericScalar_isFractionRing (j ≫ β) hcomp
  rw [hscalar] at h
  exact h

end AlgebraicGeometry.Scheme.FunctionField
