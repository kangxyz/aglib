/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.ModelTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceCompositionModel
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

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

omit [QuasiCompact f₀] in
private theorem sourceTo_at_transport (C : Hom.DenseCompactification f₀) :
    moduleUnboundedCompactificationSourceIsoTo f₀ f₁ e₁ h₁ Λ N hN hΛ C
        ((sourceIso f₁ e₁ h₁).obj C) =
      moduleUnboundedCompactificationSourceIsoModel f₀ f₁ e₁ h₁ Λ N hN hΛ C := by
  simp only [moduleUnboundedCompactificationSourceIsoTo,
      moduleUnboundedCompactificationComparison_self,
    Functor.isoWhiskerLeft_refl, Iso.trans_refl]

omit [QuasiCompact f₀] in
/-- Original source transport composition at the actual transported models, with
all three compactification model families independent. -/
theorem moduleUnboundedCompactificationSourceIsoTo_composition_model
      (C : Hom.DenseCompactification f₀) :
    SourceIsoCompositionEquation
      (moduleUnboundedCompactificationSourceIsoTo f₀ f₁ e₁ h₁ Λ N hN hΛ C
        (rawSourceFirstModel f₀ f₁ e₁ h₁ C))
      (moduleUnboundedCompactificationSourceIsoTo f₁ f₂ e₂ h₂ Λ N hN hΛ
        (rawSourceFirstModel f₀ f₁ e₁ h₁ C)
        (rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C))
      (moduleUnboundedCompactificationSourceIsoTo f₀ f₂ (e₂ ≪≫ e₁)
        (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) Λ N hN hΛ C
        (rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C))
      (𝟙 _) (moduleUnboundedDerivedInverseImageCompIso Λ e₁.hom e₂.hom) := by
  let C₂ := rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C
  let C₀₂ := rawSourceCompositeModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C
  let hOld : HasDerivedCategory.{wM₀} (ModuleSheaf C₀₂.Xbar Λ) := sourceModels C
  let : HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ) := sourceModels C
  let r := (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom
  let t := @moduleUnboundedCompactificationMixedTransition X₂ S f₂ _ Λ _ hX₂ hS
    C₂ C₀₂ r (targetModels C₂) hOld
  have hs := congrArg Iso.hom (moduleUnboundedCompactificationSourceIsoTo_refinement
    f₀ f₂ (e₂ ≪≫ e₁) (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) Λ N hN hΛ C r)
  have hm := sourceIsoComposition_absorbTarget _ _ _ t
    (moduleUnboundedDerivedInverseImageCompIso Λ e₁.hom e₂.hom) _ hs
    (moduleUnboundedCompactificationSourceIsoModel_composition_raw f₀ f₁ f₂ e₁ e₂ h₁ h₂ C Λ N hN hΛ)
  exact sourceComposition_replaceFirst _ _ _ _ _ _
    (sourceTo_at_transport f₀ f₁ e₁ h₁ Λ N hN hΛ C)
    (sourceTo_at_transport f₁ f₂ e₂ h₂ Λ N hN hΛ (rawSourceFirstModel f₀ f₁ e₁ h₁ C)) hm

variable [Nonempty (Hom.DenseCompactification f₀)]
  [Nonempty (Hom.DenseCompactification f₁)] [Nonempty (Hom.DenseCompactification f₂)]

/-- The canonical chosen source comparisons obey the original composition law,
not just an isomorphism of the source objects. -/
theorem moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_composition :
    SourceIsoCompositionEquation
      (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f₀ f₁ e₁ h₁ Λ N hN hΛ)
      (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f₁ f₂ e₂ h₂ Λ N hN hΛ)
      (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f₀ f₂ (e₂ ≪≫ e₁)
        (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) Λ N hN hΛ)
      (𝟙 _) (moduleUnboundedDerivedInverseImageCompIso Λ e₁.hom e₂.hom) := by
  let C := moduleExceptionalSuppliedCompactification f₀
  let C₁ := rawSourceFirstModel f₀ f₁ e₁ h₁ C
  let C₂ := rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C
  exact sourceIsoComposition_modelTransport _ _ _ _ _ _ _
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f₀ Λ N hN hΛ C)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f₁ Λ N hN hΛ C₁)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f₂ Λ N hN hΛ C₂)
    (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_model f₀ f₁ e₁ h₁ Λ N hN hΛ C C₁)
    (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_model f₁ f₂ e₂ h₂ Λ N hN hΛ C₁ C₂)
    (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_model f₀ f₂ (e₂ ≪≫ e₁)
      (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) Λ N hN hΛ C C₂)
    (moduleUnboundedCompactificationSourceIsoTo_composition_model f₀ f₁ f₂ e₁ e₂ h₁ h₂ Λ N hN hΛ C)

end AlgebraicGeometry.Scheme.EtaleCohomology
