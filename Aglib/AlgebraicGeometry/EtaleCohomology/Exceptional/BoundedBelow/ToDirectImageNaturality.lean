/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.ToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ToTargetWhole
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageRefinementNaturality
public import Aglib.CategoryTheory.Filtered.InvertibleDiagramTargetEquation

/-! # Descent of the original exceptional-to-ordinary comparison -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wC wD wM

section Triangles
variable (Λ : Type (u + 1)) [Ring Λ] {X C D S : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- Two original structural triangles paste by native derived associativity. -/
theorem moduleDerivedDirectImageOverIso_triangle (f : X ⟶ S)
    (jC : X ⟶ C) (jD : X ⟶ D) (a : C ⟶ D) (pC : C ⟶ S) (pD : D ⟶ S)
    (hj : jC ≫ a = jD) (hp : a ≫ pD = pC)
    (hC : jC ≫ pC = f) (hD : jD ≫ pD = f) :
    Functor.isoWhiskerLeft (moduleDerivedDirectImage Λ jC)
        (moduleDerivedDirectImageOverIso Λ pC pD a hp) ≪≫
      moduleDerivedDirectImageOverIso Λ f pC jC hC =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleDerivedDirectImageOverIso Λ jD a jC hj)
        (moduleDerivedDirectImage Λ pD) ≪≫
      moduleDerivedDirectImageOverIso Λ f pD jD hD := by
  subst jD
  simpa only [moduleDerivedDirectImageOverIso, eqToIso_refl, Iso.trans_refl] using
    moduleDerivedDirectImageOverIso_comp Λ f pC pD jC a hC hp hD
end Triangles

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- Every original refinement commutes with the original map to ordinary direct image. -/
theorem moduleCompactificationToDirectImage_refinement
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    TargetComparisonEquation (moduleCompactificationTransition Λ a)
      (moduleCompactificationToDirectImage f Λ C) (moduleCompactificationToDirectImage f Λ D) :=
  imageComparison_toTarget_whole (moduleTorsionCohomologyPlus X Λ).ι
    (moduleDerivedRefinementComparison a Λ)
    (moduleDerivedLowerShriekToDirectImage Λ C.j)
    (moduleDerivedLowerShriekToDirectImage Λ D.j)
    (moduleDerivedDirectImageOverIso Λ D.j a.hom C.j a.open_fac)
    (moduleDerivedRefinementDirectImageIso Λ a)
    (moduleDerivedDirectImageOverIso Λ f C.p C.j C.fac)
    (moduleDerivedDirectImageOverIso Λ f D.p D.j D.fac)
    (moduleDerivedProperRefinementComparison_toDirectImage_naturality
      Λ C.j D.j a.hom (Hom.DenseCompactification.isPullback_open a))
    (moduleDerivedDirectImageOverIso_triangle Λ f C.j D.j a.hom C.p D.p
      a.open_fac a.base_fac C.fac D.fac)

/-- Canonical comparison with every model preserves the same original map. -/
theorem moduleCompactificationToDirectImage_comparison (C D : Hom.DenseCompactification f) :
    TargetComparisonEquation (moduleCompactificationComparison f Λ C D).hom
      (moduleCompactificationToDirectImage f Λ D) (moduleCompactificationToDirectImage f Λ C) :=
  (moduleCompactificationDiagram (f := f) Λ).cofilteredComparison_targetEquation
    (moduleCompactificationToDirectImage f Λ)
    (fun a => moduleCompactificationToDirectImage_refinement f Λ a) C D

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- The chosen map is computed through every original compactification. -/
theorem moduleExceptionalToDirectImage_model (C : Hom.DenseCompactification f) :
    TargetComparisonEquation (moduleExceptionalDirectImagePlusIso f Λ C).hom
      (moduleCompactificationToDirectImage f Λ C) (moduleExceptionalToDirectImage f Λ) :=
  moduleCompactificationToDirectImage_comparison f Λ (moduleExceptionalCompactification f) C

end AlgebraicGeometry.Scheme.EtaleCohomology
