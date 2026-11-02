/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.ToDirectImageNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Densification

/-! # The original raw compactification comparison survives actual densification -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wC wD
variable {X S : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]

/-- The actual canonical outer-adjoint map through a raw compactification. -/
def moduleRawCompactificationToDirectImage :
    moduleRawCompactificationFunctor C Λ ⟶
      (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedDirectImage Λ f :=
  Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
    (Functor.whiskerRight (moduleDerivedLowerShriekToDirectImage Λ C.j)
      (moduleDerivedDirectImage Λ C.p) ≫
      (moduleDerivedDirectImageOverIso Λ f C.p C.j C.fac).hom)

variable [QuasiCompact C.j]
  [HasDerivedCategory.{wD} (ModuleSheaf (Hom.Compactification.densify C).Xbar Λ)]

/-- The original closed densification unit preserves the same canonical map. -/
theorem moduleRawCompactificationToDirectImage_densification :
    TargetComparisonEquation (moduleCompactificationDensificationMap C Λ)
      (moduleRawCompactificationToDirectImage
        (Hom.Compactification.densify C).toCompactification Λ)
      (moduleRawCompactificationToDirectImage C Λ) :=
  imageComparison_toTarget_whole (moduleTorsionCohomologyPlus X Λ).ι
    (moduleDerivedProperRefinementComparison (Hom.Compactification.densify C).j C.j
      (Hom.Compactification.densifyι C) (Hom.Compactification.isPullback_densify C) Λ)
    (moduleDerivedLowerShriekToDirectImage Λ (Hom.Compactification.densify C).j)
    (moduleDerivedLowerShriekToDirectImage Λ C.j)
    (moduleDerivedDirectImageOverIso Λ C.j (Hom.Compactification.densifyι C)
      (Hom.Compactification.densify C).j (Hom.Compactification.densify_j_ι C))
    (moduleDerivedDirectImageOverIso Λ (Hom.Compactification.densify C).p C.p
      (Hom.Compactification.densifyι C) (Hom.Compactification.densifyι_p C))
    (moduleDerivedDirectImageOverIso Λ f (Hom.Compactification.densify C).p
      (Hom.Compactification.densify C).j (Hom.Compactification.densify C).fac)
    (moduleDerivedDirectImageOverIso Λ f C.p C.j C.fac)
    (moduleDerivedProperRefinementComparison_toDirectImage_naturality Λ
      (Hom.Compactification.densify C).j C.j (Hom.Compactification.densifyι C)
      (Hom.Compactification.isPullback_densify C))
    (moduleDerivedDirectImageOverIso_triangle Λ f
      (Hom.Compactification.densify C).j C.j (Hom.Compactification.densifyι C)
      (Hom.Compactification.densify C).p C.p
      (Hom.Compactification.densify_j_ι C) (Hom.Compactification.densifyι_p C)
      (Hom.Compactification.densify C).fac C.fac)

end AlgebraicGeometry.Scheme.EtaleCohomology
