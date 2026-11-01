/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.NormalizationStructural
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityTripleComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CompositionCoherence

/-! # Proper normalization retains the original canonical outer-adjoint comparison -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dX dS dM
variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [Ring Λ]

/-- Ordinary identity contraction on the direct-image factorization. -/
def moduleProperDirectImageNormalizationIso :
    moduleDirectImage (𝟙 X) Λ ⋙ moduleDirectImage f Λ ≅ moduleDirectImage f Λ :=
  Functor.isoWhiskerRight (moduleDirectImageIdIso Λ X) _ ≪≫ Functor.leftUnitor _

/-- The actual ordinary outer-adjoint identity map preserves the two contractions. -/
theorem moduleProperIdentityOuterNormalization :
    Functor.isoWhiskerRight (moduleIdentityOuterIso Λ X) (moduleDirectImage f Λ) ≪≫
      moduleProperDirectImageNormalizationIso f Λ =
    Functor.isoWhiskerRight (moduleLowerShriekIdIso Λ X) (moduleDirectImage f Λ) ≪≫
      Functor.leftUnitor (moduleDirectImage f Λ) := by
  simp only [moduleIdentityOuterIso, moduleProperDirectImageNormalizationIso,
    Functor.isoWhiskerRight_trans, Iso.trans_assoc]
  change _ ≪≫ (Functor.isoWhiskerRight (moduleDirectImageIdIso Λ X)
    (moduleDirectImage f Λ)).symm ≪≫ _ ≪≫ _ = _
  rw [Iso.symm_self_id_assoc]


variable (hX : HasDerivedCategory.{dX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{dS} (ModuleSheaf S Λ))
  (hM : HasDerivedCategory.{dM} (ModuleSheaf X Λ))

/-- Original direct-image source-identity normalization, retaining independent middle models. -/
def moduleDerivedProperDirectImageNormalizationIso :
    (@rightDerivedFunctorPlus _ _ _ _ _ _ hX hM (moduleDirectImage (𝟙 X) Λ) _ _) ⋙
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hM hS (moduleDirectImage f Λ) _ _) ≅
      (@rightDerivedFunctorPlus _ _ _ _ _ _ hX hS (moduleDirectImage f Λ) _ _) :=
  @derivedCompositeNormalizeOfPreservesInjectives
    (ModuleSheaf X Λ) _ _ _ hX (ModuleSheaf X Λ) _ _ _ hM
    (ModuleSheaf S Λ) _ _ hS _ _ _ _ _ _
    (moduleProperDirectImageNormalizationIso f Λ) _

/-- This contraction is the original structural direct-image comparison. -/
theorem moduleDerivedProperDirectImageNormalizationIso_eq_over :
    moduleDerivedProperDirectImageNormalizationIso f Λ hX hS hM =
      @moduleDerivedDirectImageOverIso Λ _ S X X hS hX hM
        f f (𝟙 X) (Category.id_comp f) := by
  have h := @derivedCompositeNormalizeOfPreservesInjectives_structural
    (ModuleSheaf X Λ) _ _ _ hX (ModuleSheaf X Λ) _ _ _ hM
    (ModuleSheaf S Λ) _ _ hS
    (moduleDirectImage (𝟙 X) Λ) (moduleDirectImage f Λ)
    (moduleDirectImage f Λ) (moduleDirectImage (𝟙 X ≫ f) Λ) _ _ _ _ _
    (moduleDirectImageCompIso Λ f (𝟙 X)) (moduleProperDirectImageNormalizationIso f Λ)
    (eqToIso (congrArg (fun k : X ⟶ S => moduleDirectImage k Λ) (Category.id_comp f)))
    (moduleDirectImageCompIso_comp_id Λ f)
  simpa only [moduleDerivedProperDirectImageNormalizationIso,
    moduleDerivedDirectImageOverIso, moduleDerivedDirectImageCompIso,
    Functor.rightDerivedFunctorPlusIso_eqToIso] using h

/-- The original derived identity outer map contracts to the original proper normalization. -/
theorem moduleDerivedProperNormalizationIso_outer :
    Functor.isoWhiskerRight (moduleDerivedIdentityOuterIso Λ X hX hM)
        (@rightDerivedFunctorPlus _ _ _ _ _ _ hM hS (moduleDirectImage f Λ) _ _) ≪≫
      moduleDerivedProperDirectImageNormalizationIso f Λ hX hS hM =
      moduleDerivedProperNormalizationIso f Λ hX hS hM := by
  let : (moduleLowerShriek (𝟙 X) Λ).IsEquivalence :=
    Functor.isEquivalence_of_iso (moduleLowerShriekIdIso Λ X).symm
  have h := @derivedCompositeNormalizeOfPreservesInjectives_changeFirst
    (ModuleSheaf X Λ) _ _ _ hX (ModuleSheaf X Λ) _ _ _ hM
    (ModuleSheaf S Λ) _ _ hS
    (moduleLowerShriek (𝟙 X) Λ) (moduleDirectImage (𝟙 X) Λ)
    (moduleDirectImage f Λ) (moduleDirectImage f Λ) _ _ _ _ _ _
    (moduleIdentityOuterIso Λ X) (moduleProperDirectImageNormalizationIso f Λ)
  rw [moduleProperIdentityOuterNormalization] at h
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology
