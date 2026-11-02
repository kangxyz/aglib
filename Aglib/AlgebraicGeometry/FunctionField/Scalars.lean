/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map


/-!
# Original affine base scalars in the actual generic field

The scalar map is the preimage of the original generic structure morphism.
Its equality with the original function-field map supplies the actual fraction
ring structure for a birational model, without selecting another field.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FunctionField

variable {X : Scheme.{u}} [IsIntegral X] {A : CommRingCat.{u}}

/-- Original affine base scalars, read from the actual generic structural morphism. -/
def genericScalar (a : X ⟶ Spec A) : A ⟶ X.functionField :=
  Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ a)

/-- The scalar map is the composite through the original generic field arrow. -/
theorem genericScalar_eq_functionFieldMap [IsDomain A]
    (a : X ⟶ Spec A) [IsDominant a] :
    genericScalar a = CommRingCat.ofHom (algebraMap A (Spec A).functionField) ≫
      CommRingCat.ofHom (Scheme.functionFieldMap a) := by
  have hη : (Spec A).fromSpecStalk (genericPoint (Spec A)) =
      Spec.map (CommRingCat.ofHom (algebraMap A (Spec A).functionField)) :=
    Spec.fromSpecStalk_eq' _ _
  unfold genericScalar
  rw [Scheme.fromSpecStalk_genericPoint_naturality a, hη, ← Spec.map_comp,
    Spec.preimage_map]

/-- Changing the affine coefficient base retains the literal original ring map. -/
theorem genericScalar_comp {Λ : CommRingCat.{u}} (a : X ⟶ Spec A) (ρ : Λ ⟶ A) :
    genericScalar (a ≫ Spec.map ρ) = ρ ≫ genericScalar a := by
  unfold genericScalar
  rw [← Category.assoc, Spec.preimage_comp, Spec.preimage_map]

/-- The original scalar action commutes with the original generic map of every
actual dominant model morphism, in particular every nonempty affine chart. -/
theorem genericScalar_naturality {Y : Scheme.{u}} [IsIntegral Y]
    (a : X ⟶ Spec A) (j : Y ⟶ X) [IsDominant j] :
    genericScalar a ≫ CommRingCat.ofHom (Scheme.functionFieldMap j) =
      genericScalar (j ≫ a) := by
  let F : X.functionField ⟶ Y.functionField :=
    CommRingCat.ofHom (Scheme.functionFieldMap j)
  have htri : Spec.map F ≫ (X.fromSpecStalk (genericPoint X) ≫ a) =
      Y.fromSpecStalk (genericPoint Y) ≫ (j ≫ a) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k : Spec Y.functionField ⟶ X => k ≫ a)
        (Scheme.fromSpecStalk_genericPoint_naturality j).symm).trans
          (Category.assoc _ _ _))
  exact (congrArg (fun k : X.functionField ⟶ Y.functionField => genericScalar a ≫ k)
    (Spec.preimage_map F)).symm.trans
      ((Spec.preimage_comp (Spec.map F) (X.fromSpecStalk (genericPoint X) ≫ a)).symm.trans
        (congrArg (fun k : Spec Y.functionField ⟶ Spec A => Spec.preimage k) htri))

/-- A birational model's actual generic field is the fraction field through
its original affine structure map. -/
theorem genericScalar_isFractionRing [IsDomain A]
    (a : X ⟶ Spec A) [IsDominant a]
    (ha : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap a))) :
    letI := (genericScalar a).hom.toAlgebra
    IsFractionRing A X.functionField := by
  let := (genericScalar a).hom.toAlgebra
  let e := (@asIso CommRingCat.{u} _ (Spec A).functionField X.functionField
    (CommRingCat.ofHom (Scheme.functionFieldMap a)) ha)
  let eA : (Spec A).functionField ≃ₐ[A] X.functionField :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := by
        intro x
        exact (congrArg (fun k : A ⟶ X.functionField => k x)
          (genericScalar_eq_functionFieldMap a)).symm }
  exact IsFractionRing.of_algEquiv eA

end AlgebraicGeometry.Scheme.FunctionField
