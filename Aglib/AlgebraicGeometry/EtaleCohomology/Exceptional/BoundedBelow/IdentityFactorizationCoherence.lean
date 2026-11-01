/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitIdentityValue
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionLeftUnitIdentity
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityFactorizationCoherence
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageRefinement
public import Aglib.CategoryTheory.Functor.ImageIdentityContraction
/-! # The original epsilon under original mixed-model identity refinements -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dE dM d₀ d₁
variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  (hE : HasDerivedCategory.{dE} (ModuleSheaf X Λ))
  (hM : HasDerivedCategory.{dM} (ModuleSheaf X Λ))

/-- Original identity refinement into the endpoint model preserves the original contraction. -/
theorem moduleSingleIdentityAmbientIso_mixed_to_endpoint :
    (@moduleCompactificationMixedTransition X X (𝟙 X) _ Λ _ hE hE
      (Hom.DenseCompactification.ofProper (𝟙 X)) (Hom.DenseCompactification.ofProper (𝟙 X))
      (𝟙 _) hE hM) ≫ (moduleSingleIdentityAmbientIso X Λ hE hE).hom =
    (moduleSingleIdentityAmbientIso X Λ hE hM).hom := by
  let C := Hom.DenseCompactification.ofProper (𝟙 X)
  let δ := @moduleDerivedRefinementComparison X X (𝟙 X) _ C C (𝟙 C) Λ _ hE hE hM
  let t := @moduleDerivedRefinementDirectImageIso Λ _ X X (𝟙 X) hE C C (𝟙 C) hE hM
  have hδ := @moduleDerivedProperRefinementComparison_toDirectImage Λ _ X X (𝟙 X) _
    hE hM (Hom.DenseCompactification.isPullback_open (𝟙 C))
  have hε := moduleDerivedIdentityOuter_contraction Λ X hE hM
  have h := imageComparison_identityContraction δ t
    (@moduleDerivedLowerShriekIdIso Λ _ X hE) (@moduleDerivedDirectImageIdIso Λ _ X hE)
    (@moduleDerivedLowerShriekToDirectImage Λ _ X X (𝟙 X) _ hE hM)
    (moduleDerivedIdentityFactorizationIso Λ X hE hM) hδ hε
  change CategoryTheory.imageComparison δ t ≫
    (isoWhiskerRight (@moduleDerivedLowerShriekIdIso Λ _ X hE)
      (@moduleDerivedDirectImage X Λ _ X (𝟙 X) hE hE) ≪≫
      leftUnitor _ ≪≫ (@moduleDerivedDirectImageIdIso Λ _ X hE)).hom =
    (moduleDerivedIdentityFactorizationIso Λ X hE hM).hom at h
  rw [← @moduleDerivedIdentityFactorizationIso_sameModel X Λ _ hE] at h
  apply NatTrans.ext
  funext K
  have hk := congr_app h K.obj
  change (CategoryTheory.imageComparison δ t).app K.obj ≫
      (moduleDerivedIdentityFactorizationIso Λ X hE hE).hom.app K.obj =
    (moduleDerivedIdentityFactorizationIso Λ X hE hM).hom.app K.obj at hk
  change (CategoryTheory.imageComparison δ t).app K.obj ≫
      (moduleDerivedIdentityFactorizationIso Λ X hE hE).hom.app K.obj ≫ 𝟙 K.obj =
    (moduleDerivedIdentityFactorizationIso Λ X hE hM).hom.app K.obj ≫ 𝟙 K.obj
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ 𝟙 K.obj) hk)

variable (h₀ : HasDerivedCategory.{d₀} (ModuleSheaf X Λ))
  (h₁ : HasDerivedCategory.{d₁} (ModuleSheaf X Λ))

/-- Every original mixed-model identity transition preserves the original epsilon. -/
theorem moduleSingleIdentityAmbientIso_mixed :
    (@moduleCompactificationMixedTransition X X (𝟙 X) _ Λ _ hE hE
      (Hom.DenseCompactification.ofProper (𝟙 X)) (Hom.DenseCompactification.ofProper (𝟙 X))
      (𝟙 _) h₁ h₀) ≫ (moduleSingleIdentityAmbientIso X Λ hE h₁).hom =
    (moduleSingleIdentityAmbientIso X Λ hE h₀).hom := by
  let C := Hom.DenseCompactification.ofProper (𝟙 X)
  have hc := @moduleCompactificationMixedTransition_comp X X (𝟙 X) _ Λ _ hE hE
    C C (𝟙 C) hE h₁ C (𝟙 C) h₀
  simp only [Category.id_comp] at hc
  rw [← moduleSingleIdentityAmbientIso_mixed_to_endpoint X Λ hE h₁,
    ← Category.assoc, ← hc, moduleSingleIdentityAmbientIso_mixed_to_endpoint X Λ hE h₀]
end AlgebraicGeometry.Scheme.EtaleCohomology
