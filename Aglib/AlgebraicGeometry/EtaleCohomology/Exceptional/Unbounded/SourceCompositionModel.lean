/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSourceComposition
public import Aglib.CategoryTheory.NatTrans.SourceIsoCompositionModels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSourceIsoNaturality

/-! # Original source composition at independently modelled compactifications -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX₀ wX₁ wX₂ wS wM₀ wM₁ wM₂
variable {X₀ X₁ X₂ S : Scheme.{u}} (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
  [QuasiCompact f₀] [QuasiCompact f₁] [QuasiCompact f₂]
  (e₁ : X₁ ≅ X₀) (e₂ : X₂ ≅ X₁) (h₁ : e₁.hom ≫ f₀ = f₁)
  (h₂ : e₂.hom ≫ f₁ = f₂) (C : Hom.DenseCompactification f₀)
  (Λ : Type (u + 1)) [Ring Λ]
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

/-- The derived-category instance in universe `wM₀` for `Λ`-module sheaves on `C.Xbar`.
-/
local instance unboundedSourceCompositionOriginalModel : HasDerivedCategory.{wM₀}
    (ModuleSheaf C.Xbar Λ) := sourceModels C

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

omit [QuasiCompact f₀] in
/-- Native independent-model source comparisons satisfy the original composition
formula, before the final original refinement is absorbed into the canonical comparison. -/
theorem moduleUnboundedCompactificationSourceIsoModel_composition_raw :
    SourceIsoCompositionEquation
      (moduleUnboundedCompactificationSourceIsoModel f₀ f₁ e₁ h₁ Λ N hN hΛ C)
      (moduleUnboundedCompactificationSourceIsoModel f₁ f₂ e₂ h₂ Λ N hN hΛ
        (rawSourceFirstModel f₀ f₁ e₁ h₁ C))
      (moduleUnboundedRawCompactificationSourceIso (e₂ ≪≫ e₁) Λ f₂
        (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂) C.toCompactification)
      (@moduleUnboundedCompactificationMixedTransition X₂ S f₂ _ Λ _ hX₂ hS
        (rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C)
        (rawSourceCompositeModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C)
        (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom
        (targetModels (rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C))
        (sourceModels C))
      (moduleUnboundedDerivedInverseImageCompIso Λ e₁.hom e₂.hom) := by
  let C₁ := rawSourceFirstModel f₀ f₁ e₁ h₁ C
  let C₂ := rawSourceSequentialModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C
  let C₀₂ := rawSourceCompositeModel f₀ f₁ f₂ e₁ e₂ h₁ h₂ C
  let hOld₁ : HasDerivedCategory.{wM₀} (ModuleSheaf C₁.Xbar Λ) := sourceModels C
  let hOld₂ : HasDerivedCategory.{wM₀} (ModuleSheaf C₂.Xbar Λ) := sourceModels C
  let hMid₂ : HasDerivedCategory.{wM₁} (ModuleSheaf C₂.Xbar Λ) := middleModels C₁
  let hOld₀₂ : HasDerivedCategory.{wM₀} (ModuleSheaf C₀₂.Xbar Λ) := sourceModels C
  let m₁ := @moduleUnboundedCompactificationMixedTransition X₁ S f₁ _ Λ _ hX₁ hS
    C₁ C₁ (𝟙 C₁) (middleModels C₁) hOld₁
  let m₂ := @moduleUnboundedCompactificationMixedTransition X₂ S f₂ _ Λ _ hX₂ hS
    C₂ C₂ (𝟙 C₂) hMid₂ hOld₂
  let n₂ := @moduleUnboundedCompactificationMixedTransition X₂ S f₂ _ Λ _ hX₂ hS
    C₂ C₂ (𝟙 C₂) (targetModels C₂) hMid₂
  let r := (sourceIsoCompIso f₀ f₁ f₂ e₁ e₂ h₁ h₂ C).hom
  let t := @moduleUnboundedCompactificationMixedTransition X₂ S f₂ _ Λ _ hX₂ hS
    C₂ C₀₂ r hOld₂ hOld₀₂
  have hn := @moduleUnboundedRawCompactificationSourceIso_refinement_naturality X₁ X₂ S f₁
    e₂ f₂ h₂ C₁.toCompactification C₁.toCompactification (𝟙 C₁.Xbar)
    (isPullback_open (𝟙 C₁))
    (isPullback_open ((sourceIso f₂ e₂ h₂).map (𝟙 C₁)))
    (Category.id_comp C₁.p) Λ _ hX₁ hX₂ (middleModels C₁) hOld₁ hS
  have ht : t ≫ m₂ ≫ n₂ =
      @moduleUnboundedCompactificationMixedTransition X₂ S f₂ _ Λ _ hX₂ hS
        C₂ C₀₂ r (targetModels C₂) hOld₀₂ := by
    have hA := @moduleUnboundedCompactificationMixedTransition_comp X₂ S f₂ _ Λ _ hX₂ hS
      C₂ C₂ (𝟙 C₂) hMid₂ hOld₂ C₀₂ r hOld₀₂
    have hB := @moduleUnboundedCompactificationMixedTransition_comp X₂ S f₂ _ Λ _ hX₂ hS
      C₂ C₂ (𝟙 C₂) (targetModels C₂) hMid₂ C₀₂ r hOld₀₂
    change t ≫ m₂ ≫ n₂ = _
    rw [← Category.assoc]
    exact (congrArg (fun z => z ≫ n₂)
      (hA.symm.trans (congrArg (fun z => @moduleUnboundedCompactificationMixedTransition
        X₂ S f₂ _ Λ _ hX₂ hS C₂ C₀₂ z hMid₂ hOld₀₂) (Category.id_comp r)))).trans
      (hB.symm.trans (congrArg (fun z => @moduleUnboundedCompactificationMixedTransition
        X₂ S f₂ _ Λ _ hX₂ hS C₂ C₀₂ z (targetModels C₂) hOld₀₂) (Category.id_comp r)))
  exact sourceIsoComposition_changeMiddleModels _ _ _ t _ m₁ m₂ n₂ _ _ _ _
    (moduleUnboundedRawCompactificationSourceIso_composition f₀ f₁ f₂ e₁ e₂ h₁ h₂ C Λ)
    hn rfl rfl ht.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
