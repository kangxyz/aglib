/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageSquare
public import Aglib.CategoryTheory.Functor.ImageRightUnitStructural

/-! # The original right-unit proper-image structural triangle

The structural argument is proved for a general retraction square. In the
right-unit application the retraction maps are scheme identities, but the two
models on that scheme remain independent throughout.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wA wB wE wD
variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original over-base image triangle at the target identity has its original unit value. -/
theorem moduleDerivedDirectImageOverIso_targetIdentity
    {A E : Scheme.{u}} (q : A ⟶ E)
    [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
    [HasDerivedCategory.{wE} (ModuleSheaf E Λ)] :
    moduleDerivedDirectImageOverIso Λ q (𝟙 E) q (Category.comp_id q) =
      Functor.isoWhiskerLeft (moduleDerivedDirectImage Λ q)
        (moduleDerivedDirectImageIdIso Λ E) ≪≫
      Functor.rightUnitor (moduleDerivedDirectImage Λ q) := by
  have h := congrArg (fun e => (moduleDerivedDirectImageCompIso Λ (𝟙 E) q).symm ≪≫ e)
    (moduleDerivedDirectImageCompIso_id_comp Λ q)
  simpa only [moduleDerivedDirectImageOverIso, Iso.trans_assoc,
    Iso.symm_self_id_assoc] using h.symm

variable {A B E D : Scheme.{u}}
  (m : A ⟶ B) (p : B ⟶ D) (q : A ⟶ E) (i : E ⟶ D) (r : D ⟶ E)
  (h : q ≫ i = m ≫ p) (hi : i ≫ r = 𝟙 E) (ha : m ≫ (p ≫ r) = q)
  [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
  [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
  [HasDerivedCategory.{wE} (ModuleSheaf E Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]

/-- Two original over-base triangles give the structural retraction equation. -/
theorem moduleDerivedDirectImageSquareIso_retraction :
    RightUnitStructuralEquation
      (moduleDerivedDirectImageSquareIso Λ p q i m h)
      (moduleDerivedDirectImageCompIso Λ r p).symm
      (moduleDerivedDirectImageOverIso Λ q (p ≫ r) m ha)
      (moduleDerivedDirectImageOverIso Λ (𝟙 E) r i hi ≪≫
        moduleDerivedDirectImageIdIso Λ E) := by
  have hab : (m ≫ p) ≫ r = q := (Category.assoc m p r).trans ha
  have hab' : (q ≫ i) ≫ r = q := by rw [Category.assoc, hi, Category.comp_id]
  have hc := moduleDerivedDirectImageOverIso_comp Λ q (p ≫ r) r m p ha rfl hab
  rw [moduleDerivedDirectImageOverIso_rfl] at hc
  apply rightUnitStructuralEquation_of_rectangle
    (moduleDerivedDirectImageSquareIso Λ p q i m h)
    (moduleDerivedDirectImageCompIso Λ r p).symm
    (moduleDerivedDirectImageOverIso Λ q (p ≫ r) m ha)
    (moduleDerivedDirectImageOverIso Λ (𝟙 E) r i hi)
    (moduleDerivedDirectImageIdIso Λ E)
    (moduleDerivedDirectImageOverIso Λ q (𝟙 E) q (Category.comp_id q))
  · exact imageCompositionStructuralEquation_of_triangles
      (moduleDerivedDirectImageCompIso Λ r p).symm
      (moduleDerivedDirectImageSquareIso Λ p q i m h)
      (moduleDerivedDirectImageOverIso Λ (𝟙 E) r i hi)
      (moduleDerivedDirectImageOverIso Λ q (p ≫ r) m ha)
      (moduleDerivedDirectImageOverIso Λ q (𝟙 E) q (Category.comp_id q))
      _ _ rfl rfl
      (moduleDerivedDirectImageCompIso Λ p m)
      (moduleDerivedDirectImageCompIso Λ i q)
      (eqToIso (congrArg (fun k => moduleDerivedDirectImage Λ k) h.symm))
      (moduleDerivedDirectImageOverIso Λ q r (m ≫ p) hab)
      (moduleDerivedDirectImageOverIso Λ q r (q ≫ i) hab') hc
      (moduleDerivedDirectImageOverIso_comp Λ q (𝟙 E) r q i
        (Category.comp_id q) hi hab')
      (moduleDerivedDirectImageOverIso_transport Λ q r (m ≫ p) (q ≫ i) h.symm hab hab')
      rfl
  · exact moduleDerivedDirectImageOverIso_targetIdentity Λ q

end AlgebraicGeometry.Scheme.EtaleCohomology
