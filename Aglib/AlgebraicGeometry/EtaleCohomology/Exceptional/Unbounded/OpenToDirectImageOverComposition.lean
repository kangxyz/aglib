/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenToDirectImageComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementDirectImage
public import Aglib.CategoryTheory.Adjunction.TripleCompositionInverse

/-! # The original open comparison respects the actual structural composition contraction -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU wV wX
variable (Λ : Type (u + 1)) [Ring Λ] {U V X : Scheme.{u}}
  (j : U ⟶ V) (k : V ⟶ X) (l : U ⟶ X) (h : j ≫ k = l)
  [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- Both original structural contractions retain the same b, including the equality transport. -/
theorem moduleUnboundedLowerShriekToDirectImage_over_comp :
    OpenCompositionToTargetEquation (moduleUnboundedLowerShriekToDirectImage Λ l)
      (moduleUnboundedLowerShriekToDirectImage Λ j)
      (moduleUnboundedLowerShriekToDirectImage Λ k)
      ((moduleUnboundedDerivedLowerShriekCompIso Λ k j).symm ≪≫
        eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ h))
      (moduleUnboundedDerivedDirectImageOverIso Λ l k j h) := by
  subst l
  simpa only [eqToIso_refl, Iso.trans_refl, moduleUnboundedDerivedDirectImageOverIso] using
    openCompositionToTarget_of_square
      (moduleUnboundedLowerShriekToDirectImage Λ (j ≫ k))
      (moduleUnboundedLowerShriekToDirectImage Λ j)
      (moduleUnboundedLowerShriekToDirectImage Λ k)
      (moduleUnboundedDerivedLowerShriekCompIso Λ k j)
      (moduleUnboundedDerivedDirectImageCompIso Λ k j)
      (moduleUnboundedLowerShriekToDirectImage_comp Λ j k)
end AlgebraicGeometry.Scheme.EtaleCohomology
