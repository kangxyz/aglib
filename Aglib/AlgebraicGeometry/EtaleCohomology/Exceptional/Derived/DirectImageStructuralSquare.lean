/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageSquare

/-! # Original structural direct-image contraction around a specified square -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wA wB wC wD wZ
variable (Λ : Type (u + 1)) [Ring Λ] {A B C D Z : Scheme.{u}}
  [HasDerivedCategory.{wA} (ModuleSheaf A Λ)]
  [HasDerivedCategory.{wB} (ModuleSheaf B Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]

/-- Both actual paths contract to the same structural direct image, with all equality
transports retained and with the original square iso from the mixed-mate comparison. -/
theorem moduleDerivedDirectImageOverIso_square
    (a : A ⟶ C) (b : B ⟶ D) (v : A ⟶ B) (w : C ⟶ D)
    (pC : C ⟶ Z) (pD : D ⟶ Z) (sB : B ⟶ Z) (sA : A ⟶ Z)
    (hr : v ≫ b = a ≫ w) (hp : w ≫ pD = pC)
    (hb : b ≫ pD = sB) (ha : a ≫ pC = sA) (hv : v ≫ sB = sA) :
    ImageCompositionStructuralEquation
      (moduleDerivedDirectImageOverIso Λ pC pD w hp)
      (moduleDerivedDirectImageSquareIso Λ w v b a hr)
      (moduleDerivedDirectImageOverIso Λ sB pD b hb)
      (moduleDerivedDirectImageOverIso Λ sA pC a ha)
      (moduleDerivedDirectImageOverIso Λ sA sB v hv) := by
  have hC : (a ≫ w) ≫ pD = sA := by rw [Category.assoc, hp, ha]
  have hD : (v ≫ b) ≫ pD = sA := by rw [Category.assoc, hb, hv]
  exact imageCompositionStructuralEquation_of_triangles
    (moduleDerivedDirectImageOverIso Λ pC pD w hp)
    (moduleDerivedDirectImageSquareIso Λ w v b a hr)
    (moduleDerivedDirectImageOverIso Λ sB pD b hb)
    (moduleDerivedDirectImageOverIso Λ sA pC a ha)
    (moduleDerivedDirectImageOverIso Λ sA sB v hv)
    (moduleDerivedDirectImageOverIso Λ sB pD b hb)
    (moduleDerivedDirectImageOverIso Λ sA pC a ha) rfl rfl
    (moduleDerivedDirectImageCompIso Λ w a)
    (moduleDerivedDirectImageCompIso Λ b v)
    (eqToIso (congrArg (fun k : A ⟶ D => moduleDerivedDirectImage Λ k) hr.symm))
    (moduleDerivedDirectImageOverIso Λ sA pD (a ≫ w) hC)
    (moduleDerivedDirectImageOverIso Λ sA pD (v ≫ b) hD)
    (moduleDerivedDirectImageOverIso_comp Λ sA pC pD a w ha hp hC)
    (moduleDerivedDirectImageOverIso_comp Λ sA sB pD v b hv hb hD)
    (moduleDerivedDirectImageOverIso_transport Λ sA pD (a ≫ w) (v ≫ b) hr.symm hC hD)
    rfl
end AlgebraicGeometry.Scheme.EtaleCohomology
