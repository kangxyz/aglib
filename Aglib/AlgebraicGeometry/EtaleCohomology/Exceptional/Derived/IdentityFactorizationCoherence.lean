/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityTripleComparison
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CompositionCoherence
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExactDerivedContractionNaturality
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExactDerivedContractionPresentation
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Transport
/-! # The original identity triple map contracts through the original direct-image compositor -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dE dM
variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})

/-- Original direct-image composition, equality transport and identity, in their original order. -/
def moduleIdentityDirectContractionIso :
    moduleDirectImage (𝟙 X) Λ ⋙ moduleDirectImage (𝟙 X) Λ ≅ 𝟭 (ModuleSheaf X Λ) :=
  (moduleDirectImageCompIso Λ (𝟙 X) (𝟙 X)).symm ≪≫
    eqToIso (congrArg (fun k : X ⟶ X => moduleDirectImage k Λ) (Category.comp_id (𝟙 X))) ≪≫
    moduleDirectImageIdIso Λ X

/-- The original canonical outer comparison retains the ordinary identity contraction. -/
theorem moduleIdentityOuterIso_contraction :
    isoWhiskerRight (moduleIdentityOuterIso Λ X) (moduleDirectImage (𝟙 X) Λ) ≪≫
      moduleIdentityDirectContractionIso Λ X = moduleIdentityFactorizationIso Λ X := by
  unfold moduleIdentityDirectContractionIso
  rw [← moduleDirectImageCompIso_comp_id Λ (𝟙 X)]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [← Iso.trans_assoc, ← isoWhiskerRight_trans]
  simp only [moduleIdentityOuterIso, Iso.trans_assoc, Iso.symm_self_id,
    Iso.trans_refl, moduleIdentityFactorizationIso]

variable (hE : HasDerivedCategory.{dE} (ModuleSheaf X Λ))
  (hM : HasDerivedCategory.{dM} (ModuleSheaf X Λ))

/-- The actual original structural direct-image collapse, retaining its independent middle model. -/
def moduleDerivedIdentityDirectContractionIso :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hE hM (moduleDirectImage (𝟙 X) Λ) _ _) ⋙
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hM hE (moduleDirectImage (𝟙 X) Λ) _ _) ≅ 𝟭
        ((@DerivedCategory.Plus _ _ _ hE)) :=
  (@moduleDerivedDirectImageOverIso Λ _ X X X hE hE hM
    (𝟙 X) (𝟙 X) (𝟙 X) (Category.comp_id (𝟙 X))) ≪≫
      (@moduleDerivedDirectImageIdIso Λ _ X hE)

/-- The original compositor collapse derives its original ordinary presentation. -/
theorem moduleDerivedIdentityDirectContractionIso_eq :
    moduleDerivedIdentityDirectContractionIso Λ X hE hM =
      @exactDerivedContractionViaIso (ModuleSheaf X Λ) _ _ _ hE
        (ModuleSheaf X Λ) _ _ _ hM (moduleDirectImage (𝟙 X) Λ)
        (moduleDirectImage (𝟙 X) Λ) _ _ _ (moduleIdentityDirectContractionIso Λ X) := by
  have h := @exactDerivedContractionViaIso_presentation
    (ModuleSheaf X Λ) _ _ _ hE (ModuleSheaf X Λ) _ _ _ hM
    (moduleDirectImage (𝟙 X) Λ) (moduleDirectImage (𝟙 X) Λ)
    (moduleDirectImage (𝟙 X ≫ 𝟙 X) Λ) _ _ _ _ _
    (moduleDirectImageCompIso Λ (𝟙 X) (𝟙 X))
    (eqToIso (congrArg (fun k : X ⟶ X => moduleDirectImage k Λ) (Category.comp_id (𝟙 X))) ≪≫
      moduleDirectImageIdIso Λ X)
  simpa only [moduleDerivedIdentityDirectContractionIso, moduleDerivedDirectImageOverIso,
    moduleDerivedDirectImageCompIso, moduleDerivedDirectImageIdIso,
    rightDerivedFunctorPlusIso_trans, rightDerivedFunctorPlusIso_eqToIso,
    Iso.trans_assoc, moduleIdentityDirectContractionIso] using h

/-- The canonical original outer-adjoint map contracts to the existing epsilon, across models. -/
theorem moduleDerivedIdentityOuter_contraction :
    whiskerRight (@moduleDerivedLowerShriekToDirectImage Λ _ X X (𝟙 X) _ hE hM)
        (@moduleDerivedDirectImage X Λ _ X (𝟙 X) hE hM) ≫
      (moduleDerivedIdentityDirectContractionIso Λ X hE hM).hom =
    (moduleDerivedIdentityFactorizationIso Λ X hE hM).hom := by
  rw [moduleDerivedLowerShriekToDirectImage_identity_models]
  have h := @exactDerivedContractionViaIso_naturality
    (ModuleSheaf X Λ) _ _ _ hE (ModuleSheaf X Λ) _ _ _ hM
    (moduleLowerShriek (𝟙 X) Λ) (moduleDirectImage (𝟙 X) Λ)
    (moduleDirectImage (𝟙 X) Λ) _ _ _ _
    (moduleIdentityOuterIso Λ X) (moduleIdentityDirectContractionIso Λ X)
  rw [moduleIdentityOuterIso_contraction] at h
  rw [moduleDerivedIdentityDirectContractionIso_eq]
  exact congrArg Iso.hom h
end AlgebraicGeometry.Scheme.EtaleCohomology
