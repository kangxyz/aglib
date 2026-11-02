/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.CompositeUnitMateNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.InverseImageSquareComparison

/-!
# Actual identity-base exchange along a structural composite

The original derived exchange is the unit for the original ambient morphism,
pushed to the base through the original direct-image composition comparison.
No properness or invertibility of the ambient morphism is required.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wS wA wB
variable (Λ : Type (u + 1)) [Ring Λ]
  {S A B : Scheme.{u}} (p : A ⟶ S) (h : B ⟶ A)
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
  [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]

/-- The actual identity-base square is the original compositor after the
original inverse-image identity comparison. -/
theorem moduleUnboundedDerivedInverseImageSquareIso_composite_id :
    moduleUnboundedDerivedInverseImageSquareIso Λ p (h ≫ p) (𝟙 S) h (Category.comp_id _) =
      Functor.isoWhiskerRight (moduleUnboundedDerivedInverseImageIdIso Λ S)
        (moduleUnboundedDerivedInverseImage Λ (h ≫ p)) ≪≫
      Functor.leftUnitor (moduleUnboundedDerivedInverseImage Λ (h ≫ p)) ≪≫
      moduleUnboundedDerivedInverseImageCompIso Λ p h := by
  rw [moduleUnboundedDerivedInverseImageSquareIso_eq_comp]
  rw [← moduleUnboundedDerivedInverseImageCompIso_id_comp Λ (h ≫ p)]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- Identity-base normalization of the original module exchange, as one whole
unit equation with the actual direct-image compositor. -/
theorem moduleUnboundedDerivedBaseChangeMap_composite_id_unit :
    CompositeIdentityBaseMateEquation
      (moduleUnboundedDerivedAdjunction Λ h)
      (moduleUnboundedDerivedDirectImageCompIso Λ p h)
      (moduleUnboundedDerivedInverseImageIdIso Λ S)
      (moduleUnboundedDerivedBaseChangeMap Λ p (h ≫ p) (𝟙 S) h (Category.comp_id _)) :=
  compositeIdentityBaseMateEquation
    (moduleUnboundedDerivedAdjunction Λ p) (moduleUnboundedDerivedAdjunction Λ h)
    (moduleUnboundedDerivedAdjunction Λ (h ≫ p))
    (moduleUnboundedDerivedInverseImageCompIso Λ p h)
    (moduleUnboundedDerivedDirectImageCompIso Λ p h)
    (moduleUnboundedDerivedInverseImageIdIso Λ S)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ p h)
    (moduleUnboundedDerivedInverseImageSquareIso Λ p (h ≫ p) (𝟙 S) h (Category.comp_id _))
    (moduleUnboundedDerivedInverseImageSquareIso_composite_id Λ p h)
    (moduleUnboundedDerivedBaseChangeMap Λ p (h ≫ p) (𝟙 S) h (Category.comp_id _)) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
