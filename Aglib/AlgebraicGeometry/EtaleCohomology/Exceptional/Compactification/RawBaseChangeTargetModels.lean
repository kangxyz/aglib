/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CompositeTargetRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawTargetModels
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangeTargetModels

/-! # Original raw compactification base change under target-model transport -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wC wX' wR wT₀ wT₁
variable {X S T : Scheme.{u}} {f : X ⟶ S} (C : Hom.Compactification f) (b : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))
  (hX' : HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ))
  (hR : HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
  (hT₀ : HasDerivedCategory.{wT₀} (ModuleSheaf T Λ))
  (hT₁ : HasDerivedCategory.{wT₁} (ModuleSheaf T Λ))

/-- The unchanged original raw exchange respects canonical native target transport. -/
theorem moduleRawCompactificationBaseChangeIso_targetModel :
    Functor.isoWhiskerRight
        (@moduleRawCompactificationBaseChangeIso X S T f C b Λ _ hX hS hC hX' hR hT₀)
        (canonicalEquivalence hT₀ hT₁).functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (@moduleDerivedInverseImageTorsion (pullback b f) X (pullback.snd b f) Λ _ hX' hX)
        (moduleRawCompactificationTargetComparison (C.baseChange b) Λ hX' hT₀ hT₁ hR) =
    imageTargetIso (@moduleRawCompactificationFunctor X S f C Λ _ hX hS hC)
        (Functor.rightDerivedFunctorPlusChangeTarget hS hT₀ hT₁ (moduleInverseImage b Λ)) ≪≫
      @moduleRawCompactificationBaseChangeIso X S T f C b Λ _ hX hS hC hX' hR hT₁ := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    moduleRawCompactificationTargetComparison, imageTargetIso, Category.assoc]
  exact compositeExchange_target_restriction
    (@moduleDerivedBaseChangeMap Λ _ C.Xbar S (pullback b C.p) T hC hS hR hT₀
      C.p (pullback.fst b C.p) b (pullback.snd b C.p)
      (IsPullback.of_hasPullback b C.p).flip.w.symm)
    (@moduleDerivedBaseChangeMap Λ _ C.Xbar S (pullback b C.p) T hC hS hR hT₁
      C.p (pullback.fst b C.p) b (pullback.snd b C.p)
      (IsPullback.of_hasPullback b C.p).flip.w.symm)
    (@moduleDerivedLowerShriekCartesianBaseChangeIso
      (pullback b f) X (C.baseChange b).Xbar C.Xbar
      (pullback.snd b f) (C.baseChange b).j C.j (pullback.snd b C.p) _ _
      (isPullback_rawCompactificationOpen C b) Λ _ hX' hX hR hC)
    (@moduleDerivedInverseImageTorsionForgetIso (pullback b f) X (pullback.snd b f)
      Λ _ hX' hX).symm
    (Functor.rightDerivedFunctorPlusChangeTarget hS hT₀ hT₁ (moduleInverseImage b Λ))
    (moduleDerivedDirectImageTargetIso Λ hR hT₀ hT₁ (pullback.fst b C.p))
    (moduleDerivedBaseChangeMap_targetModel Λ hC hS hR hT₀ hT₁
      C.p (pullback.fst b C.p) b (pullback.snd b C.p)
      (IsPullback.of_hasPullback b C.p).flip.w.symm)
    (@moduleRawCompactificationBaseChangeIso X S T f C b Λ _ hX hS hC hX' hR hT₀).hom
    (@moduleRawCompactificationBaseChangeIso X S T f C b Λ _ hX hS hC hX' hR hT₁).hom
    (@moduleRawCompactificationBaseChangeIso_hom_fac X S T f C b Λ _ hX hS hC hX' hT₀ hR)
    (@moduleRawCompactificationBaseChangeIso_hom_fac X S T f C b Λ _ hX hS hC hX' hT₁ hR)

end AlgebraicGeometry.Scheme.EtaleCohomology
