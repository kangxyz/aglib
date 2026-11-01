/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.ModelTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceCompositionModel
public import Aglib.CategoryTheory.NatTrans.SourceIsoCompositionTransport

/-! # Canonical source-isomorphism composition for exceptional direct image -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX₀ wX₁ wX₂ wS wM₀ wM₁ wM₂
variable {X₀ X₁ X₂ S : Scheme.{u}} (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
  [QuasiCompact f₀] [QuasiCompact f₁] [QuasiCompact f₂]
  (e₁ : X₁ ≅ X₀) (e₂ : X₂ ≅ X₁) (h₁ : e₁.hom ≫ f₀ = f₁)
  (h₂ : e₂.hom ≫ f₁ = f₂) (Λ : Type (u + 1)) [Ring Λ]
  [hX₀ : HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [hX₁ : HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [hX₂ : HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [sourceModels : ∀ D : Hom.DenseCompactification f₀,
    HasDerivedCategory.{wM₀} (ModuleSheaf D.Xbar Λ)]
  [middleModels : ∀ D : Hom.DenseCompactification f₁,
    HasDerivedCategory.{wM₁} (ModuleSheaf D.Xbar Λ)]
  [targetModels : ∀ D : Hom.DenseCompactification f₂,
    HasDerivedCategory.{wM₂} (ModuleSheaf D.Xbar Λ)]

omit [QuasiCompact f₀] in
private theorem sourceTo_at_transport (C : Hom.DenseCompactification f₀) :
    moduleCompactificationSourceIsoTo f₀ f₁ e₁ h₁ Λ C
        ((sourceIso f₁ e₁ h₁).obj C) =
      moduleCompactificationSourceIsoModel f₀ f₁ e₁ h₁ Λ C := by
  simp only [moduleCompactificationSourceIsoTo, moduleCompactificationComparison_self,
    Functor.isoWhiskerLeft_refl, Iso.trans_refl]

omit [QuasiCompact f₀] in
/-- Original source transport composition at the actual transported models, with
all three compactification model families independent. -/
theorem moduleCompactificationSourceIsoTo_composition_model (C : Hom.DenseCompactification f₀) :
    SourceIsoCompositionEquation
      (moduleCompactificationSourceIsoTo f₀ f₁ e₁ h₁ Λ C
        (rawSourceFirstModel f₀ f₁ e₁ h₁ C))
      (moduleCompactificationSourceIsoTo f₁ f₂ e₂ h₂ Λ
        (rawSourceFirstModel f₀ f₁ e₁ h₁ C)
        (rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C))
      (moduleCompactificationSourceIsoTo f₀ f₂ (e₂ ≪≫ e₁)
        (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) Λ C
        (rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C))
      (𝟙 _) (moduleDerivedInverseImageTorsionCompIso Λ e₁.hom e₂.hom) := by
  let C₂ := rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C
  let C₀₂ := rawSourceCompositeModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C
  let hOld : HasDerivedCategory.{wM₀} (ModuleSheaf C₀₂.Xbar Λ) := sourceModels C
  let : HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ) := sourceModels C
  let r := (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom
  let t := @moduleCompactificationMixedTransition X₂ S f₂ _ Λ _ hX₂ hS
    C₂ C₀₂ r (targetModels C₂) hOld
  have hs := congrArg Iso.hom (moduleCompactificationSourceIsoTo_refinement
    f₀ f₂ (e₂ ≪≫ e₁) (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) Λ C r)
  have hm := sourceIsoComposition_absorbTarget _ _ _ t
    (moduleDerivedInverseImageTorsionCompIso Λ e₁.hom e₂.hom) _ hs
    (moduleCompactificationSourceIsoModel_composition_raw f₀ f₁ f₂ e₁ e₂ h₁ h₂ C Λ)
  exact sourceComposition_replaceFirst _ _ _ _ _ _
    (sourceTo_at_transport f₀ f₁ e₁ h₁ Λ C)
    (sourceTo_at_transport f₁ f₂ e₂ h₂ Λ (rawSourceFirstModel f₀ f₁ e₁ h₁ C)) hm

variable [Nonempty (Hom.DenseCompactification f₀)]
  [Nonempty (Hom.DenseCompactification f₁)] [Nonempty (Hom.DenseCompactification f₂)]

/-- The canonical chosen source comparisons obey the original composition law,
not just an isomorphism of the source objects. -/
theorem moduleExceptionalDirectImagePlusSourceIsoOfNonempty_composition :
    SourceIsoCompositionEquation
      (moduleExceptionalDirectImagePlusSourceIsoOfNonempty f₀ f₁ e₁ h₁ Λ)
      (moduleExceptionalDirectImagePlusSourceIsoOfNonempty f₁ f₂ e₂ h₂ Λ)
      (moduleExceptionalDirectImagePlusSourceIsoOfNonempty f₀ f₂ (e₂ ≪≫ e₁)
        (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) Λ)
      (𝟙 _) (moduleDerivedInverseImageTorsionCompIso Λ e₁.hom e₂.hom) := by
  let C := moduleExceptionalSuppliedCompactification f₀
  let C₁ := rawSourceFirstModel f₀ f₁ e₁ h₁ C
  let C₂ := rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C
  exact sourceIsoComposition_modelTransport _ _ _ _ _ _ _
    (moduleExceptionalDirectImagePlusOfNonemptyIso f₀ Λ C)
    (moduleExceptionalDirectImagePlusOfNonemptyIso f₁ Λ C₁)
    (moduleExceptionalDirectImagePlusOfNonemptyIso f₂ Λ C₂)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty_model f₀ f₁ e₁ h₁ Λ C C₁)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty_model f₁ f₂ e₂ h₂ Λ C₁ C₂)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty_model f₀ f₂ (e₂ ≪≫ e₁)
      (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) Λ C C₂)
    (moduleCompactificationSourceIsoTo_composition_model f₀ f₁ f₂ e₁ e₂ h₁ h₂ Λ C)

end AlgebraicGeometry.Scheme.EtaleCohomology
