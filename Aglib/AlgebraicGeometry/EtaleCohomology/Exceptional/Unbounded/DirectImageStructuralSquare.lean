/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionRefinementDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImageSquare

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
theorem moduleUnboundedDerivedDirectImageOverIso_square
    (a : A ⟶ C) (b : B ⟶ D) (v : A ⟶ B) (w : C ⟶ D)
    (pC : C ⟶ Z) (pD : D ⟶ Z) (sB : B ⟶ Z) (sA : A ⟶ Z)
    (hr : v ≫ b = a ≫ w) (hp : w ≫ pD = pC)
    (hb : b ≫ pD = sB) (ha : a ≫ pC = sA) (hv : v ≫ sB = sA) :
    ImageCompositionStructuralEquation
      (moduleUnboundedDerivedDirectImageOverIso Λ pC pD w hp)
      (moduleUnboundedDerivedDirectImageSquareIso Λ w v b a hr)
      (moduleUnboundedDerivedDirectImageOverIso Λ sB pD b hb)
      (moduleUnboundedDerivedDirectImageOverIso Λ sA pC a ha)
      (moduleUnboundedDerivedDirectImageOverIso Λ sA sB v hv) := by
  have hC : (a ≫ w) ≫ pD = sA := by rw [Category.assoc, hp, ha]
  have hD : (v ≫ b) ≫ pD = sA := by rw [Category.assoc, hb, hv]
  exact imageCompositionStructuralEquation_of_triangles
    (moduleUnboundedDerivedDirectImageOverIso Λ pC pD w hp)
    (moduleUnboundedDerivedDirectImageSquareIso Λ w v b a hr)
    (moduleUnboundedDerivedDirectImageOverIso Λ sB pD b hb)
    (moduleUnboundedDerivedDirectImageOverIso Λ sA pC a ha)
    (moduleUnboundedDerivedDirectImageOverIso Λ sA sB v hv)
    (moduleUnboundedDerivedDirectImageOverIso Λ sB pD b hb)
    (moduleUnboundedDerivedDirectImageOverIso Λ sA pC a ha) rfl rfl
    (moduleUnboundedDerivedDirectImageCompIso Λ w a)
    (moduleUnboundedDerivedDirectImageCompIso Λ b v)
    (eqToIso (congrArg (fun k : A ⟶ D => moduleUnboundedDerivedDirectImage Λ k) hr.symm))
    (moduleUnboundedDerivedDirectImageOverIso Λ sA pD (a ≫ w) hC)
    (moduleUnboundedDerivedDirectImageOverIso Λ sA pD (v ≫ b) hD)
    (moduleUnboundedDerivedDirectImageOverIso_comp Λ sA pC pD a w ha hp hC)
    (moduleUnboundedDerivedDirectImageOverIso_comp Λ sA sB pD v b hv hb hD)
    (moduleUnboundedDerivedDirectImageOverIso_transport
      Λ sA pD (a ≫ w) (v ≫ b) hr.symm hC hD)
    rfl
end AlgebraicGeometry.Scheme.EtaleCohomology
