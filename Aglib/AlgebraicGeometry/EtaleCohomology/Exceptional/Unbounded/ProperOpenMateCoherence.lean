/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenComparisonPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenMate

/-! # Coherence of the original proper/open mate

The literal mixed mate is defined on all unbounded inputs. Its pasting uses
actual inverse/direct-image compositors and the proved Cartesian open-square
pasting equation. Properness and torsion are needed for invertibility, not for
this map-level coherence law.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU₀ wU₁ wU₂ wX₀ wX₁ wX₂

variable (Λ : Type (u + 1)) [Ring Λ]

section Vertical

variable {U₀ U₁ U₂ X₀ X₁ X₂ : Scheme.{u}}
  (j₀ : U₀ ⟶ X₀) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
  (g₁ : U₁ ⟶ U₀) (g₂ : U₂ ⟶ U₁) (f₁ : X₁ ⟶ X₀) (f₂ : X₂ ⟶ X₁)
  [Etale j₀] [Etale j₁] [Etale j₂]
  (h₁ : IsPullback g₁ j₁ j₀ f₁) (h₂ : IsPullback g₂ j₂ j₁ f₂)
  (ht : IsPullback (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁))
  [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
  [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
  [HasDerivedCategory.{wU₂} (ModuleSheaf U₂ Λ)]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]

/-- Pasting the actual open Cartesian squares and then taking their original
mixed mates is the same as pasting those mates with the original direct-image
compositors. The square-pasting premise is supplied by the proved open law. -/
theorem moduleUnboundedProperOpenMate_vComp_mate
    (K : DerivedCategory (ModuleSheaf U₂ Λ)) :
    VerticalMateEquation
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g₁ j₁ j₀ f₁ h₁ Λ).hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g₂ j₂ j₁ f₂ h₂ Λ).hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso
          (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁) ht Λ).hom)
      (moduleUnboundedDerivedDirectImageCompIso Λ g₁ g₂)
      (moduleUnboundedDerivedDirectImageCompIso Λ f₁ f₂)
      (moduleUnboundedDerivedAdjunction Λ g₁) (moduleUnboundedDerivedAdjunction Λ f₁)
      (moduleUnboundedDerivedAdjunction Λ g₂) (moduleUnboundedDerivedAdjunction Λ f₂)
      (moduleUnboundedDerivedAdjunction Λ (g₂ ≫ g₁))
      (moduleUnboundedDerivedAdjunction Λ (f₂ ≫ f₁)) K :=
  verticalMateEquation
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g₁ j₁ j₀ f₁ h₁ Λ).hom)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g₂ j₂ j₁ f₂ h₂ Λ).hom)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso
        (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁) ht Λ).hom)
    (moduleUnboundedDerivedInverseImageCompIso Λ g₁ g₂)
    (moduleUnboundedDerivedInverseImageCompIso Λ f₁ f₂)
    (moduleUnboundedDerivedDirectImageCompIso Λ g₁ g₂)
    (moduleUnboundedDerivedDirectImageCompIso Λ f₁ f₂)
    (moduleUnboundedDerivedAdjunction Λ g₁) (moduleUnboundedDerivedAdjunction Λ f₁)
    (moduleUnboundedDerivedAdjunction Λ g₂) (moduleUnboundedDerivedAdjunction Λ f₂)
    (moduleUnboundedDerivedAdjunction Λ (g₂ ≫ g₁))
    (moduleUnboundedDerivedAdjunction Λ (f₂ ≫ f₁))
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ g₁ g₂)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ f₁ f₂)
    (moduleUnboundedDerivedOpenComparison_pasting j₀ j₁ j₂ g₁ g₂ f₁ f₂ h₁ h₂ ht Λ) K

/-- Explicit component form of the actual vertical proper/open mate law. -/
theorem moduleUnboundedProperOpenMate_vComp
    (K : DerivedCategory (ModuleSheaf U₂ Λ)) :
    (moduleUnboundedDerivedLowerShriek j₀ Λ).map
        ((moduleUnboundedDerivedDirectImageCompIso Λ g₁ g₂).hom.app K) ≫
      (moduleUnboundedProperOpenMate g₁ j₁ j₀ f₁ h₁ Λ).app
        ((moduleUnboundedDerivedDirectImage Λ g₂).obj K) ≫
      (moduleUnboundedDerivedDirectImage Λ f₁).map
        ((moduleUnboundedProperOpenMate g₂ j₂ j₁ f₂ h₂ Λ).app K) =
    (moduleUnboundedProperOpenMate (g₂ ≫ g₁) j₂ j₀ (f₂ ≫ f₁) ht Λ).app K ≫
      (moduleUnboundedDerivedDirectImageCompIso Λ f₁ f₂).hom.app
        ((moduleUnboundedDerivedLowerShriek j₂ Λ).obj K) :=
  moduleUnboundedProperOpenMate_vComp_mate Λ j₀ j₁ j₂ g₁ g₂ f₁ f₂ h₁ h₂ ht K

end Vertical

end AlgebraicGeometry.Scheme.EtaleCohomology
