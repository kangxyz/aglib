/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.MixedModelTransition

/-! # The same canonical comparison for independent middle-model refinements -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wC wD
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  {C D : Hom.DenseCompactification f} (a : C ⟶ D)
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

/-- Actual refinement preserves b even when the same scheme carries independent models. -/
theorem moduleUnboundedCompactificationMixedTransition_toDirectImage :
    TargetComparisonEquation (moduleUnboundedCompactificationMixedTransition Λ a)
      (moduleUnboundedRawCompactificationToDirectImage C.toCompactification Λ)
      (moduleUnboundedRawCompactificationToDirectImage D.toCompactification Λ) :=
  imageComparison_toTarget_equation
    (moduleUnboundedDerivedRefinementComparison a Λ)
    (moduleUnboundedLowerShriekToDirectImage Λ C.j)
    (moduleUnboundedLowerShriekToDirectImage Λ D.j)
    (moduleUnboundedDerivedDirectImageOverIso Λ D.j a.hom C.j a.open_fac)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a)
    (moduleUnboundedDerivedDirectImageOverIso Λ f C.p C.j C.fac)
    (moduleUnboundedDerivedDirectImageOverIso Λ f D.p D.j D.fac)
    (moduleUnboundedDerivedProperRefinementComparison_toDirectImage_naturality
      Λ C.j D.j a.hom (Hom.DenseCompactification.isPullback_open a))
    (moduleUnboundedDerivedDirectImageOverIso_triangle Λ f C.j D.j a.hom C.p D.p
      a.open_fac a.base_fac C.fac D.fac)

end AlgebraicGeometry.Scheme.EtaleCohomology
