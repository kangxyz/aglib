/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.TargetExchangeNormalization
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChangeTargetModels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChange

/-! # Original normalized base change under independent target-model transport -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wC wX' wR wN wT₀ wT₁
variable {X S T : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (b : T ⟶ S) (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))
  (hX' : HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ))
  (hR : HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
  (hN : HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b C).Xbar Λ))
  (hT₀ : HasDerivedCategory.{wT₀} (ModuleSheaf T Λ))
  (hT₁ : HasDerivedCategory.{wT₁} (ModuleSheaf T Λ))

/-- The original raw exchange and closed-densification map jointly respect target transport. -/
theorem moduleNormalizedCompactificationBaseChangeIso_targetModel :
    Functor.isoWhiskerRight
        (@moduleNormalizedCompactificationBaseChangeIso X S T f _ C b Λ _
          hX hS hC hX' hT₀ hR hN) (canonicalEquivalence hT₀ hT₁).functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (@moduleDerivedInverseImageTorsion (pullback b f) X (pullback.snd b f) Λ _ hX' hX)
        (moduleRawCompactificationTargetComparison
          (Hom.DenseCompactification.baseChangeObj b C).toCompactification
          Λ hX' hT₀ hT₁ hN) =
    imageTargetIso (@moduleRawCompactificationFunctor X S f C.toCompactification Λ _ hX hS hC)
        (Functor.rightDerivedFunctorPlusChangeTarget hS hT₀ hT₁ (moduleInverseImage b Λ)) ≪≫
      @moduleNormalizedCompactificationBaseChangeIso X S T f _ C b Λ _
        hX hS hC hX' hT₁ hR hN :=
  targetExchange_postcomp_normalized
    (@moduleRawCompactificationBaseChangeIso X S T f C.toCompactification b Λ _
      hX hS hC hX' hR hT₀)
    (@moduleRawCompactificationBaseChangeIso X S T f C.toCompactification b Λ _
      hX hS hC hX' hR hT₁)
    (@moduleCompactificationDensificationIso (pullback b f) T (pullback.fst b f)
      (C.toCompactification.baseChange b) _ Λ _ hX' hT₀ hR hN)
    (@moduleCompactificationDensificationIso (pullback b f) T (pullback.fst b f)
      (C.toCompactification.baseChange b) _ Λ _ hX' hT₁ hR hN)
    (Functor.rightDerivedFunctorPlusChangeTarget hS hT₀ hT₁ (moduleInverseImage b Λ))
    (moduleRawCompactificationTargetComparison (C.toCompactification.baseChange b)
      Λ hX' hT₀ hT₁ hR)
    (moduleRawCompactificationTargetComparison
      (Hom.DenseCompactification.baseChangeObj b C).toCompactification Λ hX' hT₀ hT₁ hN)
    (imageTargetIso (@moduleRawCompactificationFunctor X S f C.toCompactification Λ _ hX hS hC)
      (Functor.rightDerivedFunctorPlusChangeTarget hS hT₀ hT₁ (moduleInverseImage b Λ))) rfl
    (moduleRawCompactificationBaseChangeIso_targetModel C.toCompactification b Λ
      hX hS hC hX' hR hT₀ hT₁)
    (moduleCompactificationDensification_targetModel (C.toCompactification.baseChange b)
      Λ hX' hT₀ hT₁ hR hN)

end AlgebraicGeometry.Scheme.EtaleCohomology
