/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TargetModelComparison
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedTargetModels

/-! # Chosen original base change under canonical independent target-model transport -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wX' wM wN wR wT₀ wT₁
variable {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)] (b : T ⟶ S)
local instance : Nonempty (Hom.DenseCompactification (pullback.fst b f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f)⟩
variable (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (hX' : HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ))
  (hT₀ : HasDerivedCategory.{wT₀} (ModuleSheaf T Λ))
  (hT₁ : HasDerivedCategory.{wT₁} (ModuleSheaf T Λ))
  (sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
  (targetModels : ∀ D : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ))
  (rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))

omit [Nonempty (Hom.DenseCompactification f)] in
/-- Original normalized model base change commutes with canonical native target transport. -/
theorem moduleCompactificationBaseChangeIsoTo_targetModel
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification (pullback.fst b f)) :
    Functor.isoWhiskerRight
        (@moduleCompactificationBaseChangeIsoTo X S T f _ b Λ _
          hX hS hX' hT₀ sourceModels targetModels rawModels C D)
        (canonicalEquivalence hT₀ hT₁).functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (@moduleDerivedInverseImageTorsion (pullback b f) X (pullback.snd b f) Λ _ hX' hX)
        (moduleCompactificationTargetComparison (pullback.fst b f) Λ hX' hT₀ hT₁ targetModels D) =
    imageTargetIso ((@moduleCompactificationFunctor X S f Λ _ hX hS C (sourceModels C)))
        (Functor.rightDerivedFunctorPlusChangeTarget hS hT₀ hT₁ (moduleInverseImage b Λ)) ≪≫
      @moduleCompactificationBaseChangeIsoTo X S T f _ b Λ _
        hX hS hX' hT₁ sourceModels targetModels rawModels C D :=
  targetExchange_postcomp_normalized
    (@moduleNormalizedCompactificationBaseChangeIso X S T f _ C b Λ _
      hX hS (sourceModels C) hX' hT₀ (rawModels C)
      (targetModels (Hom.DenseCompactification.baseChangeObj b C)))
    (@moduleNormalizedCompactificationBaseChangeIso X S T f _ C b Λ _
      hX hS (sourceModels C) hX' hT₁ (rawModels C)
      (targetModels (Hom.DenseCompactification.baseChangeObj b C)))
    (@moduleCompactificationComparison (pullback b f) T (pullback.fst b f) _ Λ _
      hX' hT₀ targetModels (Hom.DenseCompactification.baseChangeObj b C) D)
    (@moduleCompactificationComparison (pullback b f) T (pullback.fst b f) _ Λ _
      hX' hT₁ targetModels (Hom.DenseCompactification.baseChangeObj b C) D)
    (Functor.rightDerivedFunctorPlusChangeTarget hS hT₀ hT₁ (moduleInverseImage b Λ))
    (moduleCompactificationTargetComparison (pullback.fst b f) Λ hX' hT₀ hT₁ targetModels
      (Hom.DenseCompactification.baseChangeObj b C))
    (moduleCompactificationTargetComparison (pullback.fst b f) Λ hX' hT₀ hT₁ targetModels D)
    (imageTargetIso ((@moduleCompactificationFunctor X S f Λ _ hX hS C (sourceModels C)))
      (Functor.rightDerivedFunctorPlusChangeTarget hS hT₀ hT₁ (moduleInverseImage b Λ))) rfl
    (moduleNormalizedCompactificationBaseChangeIso_targetModel C b Λ hX hS (sourceModels C)
      hX' (rawModels C) (targetModels (Hom.DenseCompactification.baseChangeObj b C)) hT₀ hT₁)
    (moduleCompactificationTargetComparison_canonical (pullback.fst b f) Λ
      hX' hT₀ hT₁ targetModels (Hom.DenseCompactification.baseChangeObj b C) D).symm

/-- The actual chosen base-change isomorphism retains the original native target-model square. -/
theorem moduleExceptionalBaseChange_targetModel :
    Functor.isoWhiskerRight
        (@moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty X S T f _ _ b Λ _
          hX hS hX' hT₀ sourceModels targetModels rawModels)
        (canonicalEquivalence hT₀ hT₁).functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (@moduleDerivedInverseImageTorsion (pullback b f) X (pullback.snd b f) Λ _ hX' hX)
        (moduleExceptionalTargetComparison (pullback.fst b f) Λ hX' hT₀ hT₁ targetModels) =
    imageTargetIso ((@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS (sourceModels
      (moduleExceptionalSuppliedCompactification f))))
        (Functor.rightDerivedFunctorPlusChangeTarget hS hT₀ hT₁ (moduleInverseImage b Λ)) ≪≫
      @moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty X S T f _ _ b Λ _
        hX hS hX' hT₁ sourceModels targetModels rawModels :=
  moduleCompactificationBaseChangeIsoTo_targetModel f b Λ hX hS hX' hT₀ hT₁
    sourceModels targetModels rawModels
    (moduleExceptionalSuppliedCompactification f)
    (moduleExceptionalSuppliedCompactification (pullback.fst b f))

end AlgebraicGeometry.Scheme.EtaleCohomology
