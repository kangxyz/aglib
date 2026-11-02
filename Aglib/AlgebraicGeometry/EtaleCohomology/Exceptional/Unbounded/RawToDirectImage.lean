/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ToDirectImageNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Densification

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
def moduleUnboundedRawCompactificationToDirectImage :
    moduleUnboundedRawCompactificationFunctor C Λ ⟶
      moduleUnboundedDerivedDirectImage Λ f :=
  Functor.whiskerRight (moduleUnboundedLowerShriekToDirectImage Λ C.j)
      (moduleUnboundedDerivedDirectImage Λ C.p) ≫
    (moduleUnboundedDerivedDirectImageOverIso Λ f C.p C.j C.fac).hom

variable [QuasiCompact C.j]
  [HasDerivedCategory.{wD} (ModuleSheaf (Hom.Compactification.densify C).Xbar Λ)]

/-- The original closed densification unit preserves the same canonical map. -/
theorem moduleUnboundedRawCompactificationToDirectImage_densification :
    TargetComparisonEquation (moduleUnboundedCompactificationDensificationMap C Λ)
      (moduleUnboundedRawCompactificationToDirectImage
        (Hom.Compactification.densify C).toCompactification Λ)
      (moduleUnboundedRawCompactificationToDirectImage C Λ) :=
  imageComparison_toTarget_equation
    (moduleUnboundedDerivedProperRefinementComparison (Hom.Compactification.densify C).j C.j
      (Hom.Compactification.densifyι C) (Hom.Compactification.isPullback_densify C) Λ)
    (moduleUnboundedLowerShriekToDirectImage Λ (Hom.Compactification.densify C).j)
    (moduleUnboundedLowerShriekToDirectImage Λ C.j)
    (moduleUnboundedDerivedDirectImageOverIso Λ C.j (Hom.Compactification.densifyι C)
      (Hom.Compactification.densify C).j (Hom.Compactification.densify_j_ι C))
    (moduleUnboundedDerivedDirectImageOverIso Λ (Hom.Compactification.densify C).p C.p
      (Hom.Compactification.densifyι C) (Hom.Compactification.densifyι_p C))
    (moduleUnboundedDerivedDirectImageOverIso Λ f (Hom.Compactification.densify C).p
      (Hom.Compactification.densify C).j (Hom.Compactification.densify C).fac)
    (moduleUnboundedDerivedDirectImageOverIso Λ f C.p C.j C.fac)
    (moduleUnboundedDerivedProperRefinementComparison_toDirectImage_naturality Λ
      (Hom.Compactification.densify C).j C.j (Hom.Compactification.densifyι C)
      (Hom.Compactification.isPullback_densify C))
    (moduleUnboundedDerivedDirectImageOverIso_triangle Λ f
      (Hom.Compactification.densify C).j C.j (Hom.Compactification.densifyι C)
      (Hom.Compactification.densify C).p C.p
      (Hom.Compactification.densify_j_ι C) (Hom.Compactification.densifyι_p C)
      (Hom.Compactification.densify C).fac C.fac)

end AlgebraicGeometry.Scheme.EtaleCohomology
