/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.CompositeUnitMateNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangeIdentity

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
theorem moduleDerivedInverseImageSquareIso_composite_id :
    moduleDerivedInverseImageSquareIso Λ p (h ≫ p) (𝟙 S) h (Category.comp_id _) =
      Functor.isoWhiskerRight (moduleDerivedInverseImageIdIso Λ S)
        (moduleDerivedInverseImage Λ (h ≫ p)) ≪≫
      Functor.leftUnitor (moduleDerivedInverseImage Λ (h ≫ p)) ≪≫
      moduleDerivedInverseImageCompIso Λ p h := by
  unfold moduleDerivedInverseImageSquareIso
  rw [← moduleDerivedInverseImageCompIso_id_comp Λ (h ≫ p)]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- Identity-base normalization of the original module exchange, as one whole
unit equation with the actual direct-image compositor. -/
theorem moduleDerivedBaseChangeMap_composite_id_unit :
    CompositeIdentityBaseMateEquation
      (moduleDerivedAdjunction Λ h)
      (moduleDerivedDirectImageCompIso Λ p h)
      (moduleDerivedInverseImageIdIso Λ S)
      (moduleDerivedBaseChangeMap Λ p (h ≫ p) (𝟙 S) h (Category.comp_id _)) :=
  compositeIdentityBaseMateEquation
    (moduleDerivedAdjunction Λ p) (moduleDerivedAdjunction Λ h)
    (moduleDerivedAdjunction Λ (h ≫ p))
    (moduleDerivedInverseImageCompIso Λ p h)
    (moduleDerivedDirectImageCompIso Λ p h)
    (moduleDerivedInverseImageIdIso Λ S)
    (conjugateEquiv_moduleDerivedInverseImageCompIso_hom Λ p h)
    (moduleDerivedInverseImageSquareIso Λ p (h ≫ p) (𝟙 S) h (Category.comp_id _))
    (moduleDerivedInverseImageSquareIso_composite_id Λ p h)
    (moduleDerivedBaseChangeMap Λ p (h ≫ p) (𝟙 S) h (Category.comp_id _)) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
