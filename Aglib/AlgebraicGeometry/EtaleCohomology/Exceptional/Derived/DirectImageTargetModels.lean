/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CompositionCoherence
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetTransport

/-! # Original direct-image compositors under canonical target-model transport -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wC wD wS₀ wS₁
variable (Λ : Type (u + 1)) [Ring Λ] {C D S : Scheme.{u}}
  (hC : HasDerivedCategory.{wC} (ModuleSheaf C Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf D Λ))
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  (hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ))

/-- Canonical target-model transport of the actual derived module direct image. -/
abbrev moduleDerivedDirectImageTargetIso (p : C ⟶ S) :=
  Functor.rightDerivedFunctorPlusChangeTarget hC hS₀ hS₁ (moduleDirectImage p Λ)

/-- The original direct-image compositor commutes with canonical target-model comparison. -/
theorem moduleDerivedDirectImageTargetIso_comp (p : D ⟶ S) (a : C ⟶ D) :
    Functor.isoWhiskerRight (@moduleDerivedDirectImageCompIso Λ _ S D C p a hS₀ hD hC)
        (canonicalEquivalence hS₀ hS₁).functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hC hD
        (moduleDirectImage a Λ) _ _))
        (moduleDerivedDirectImageTargetIso Λ hD hS₀ hS₁ p) =
    moduleDerivedDirectImageTargetIso Λ hC hS₀ hS₁ (a ≫ p) ≪≫
      @moduleDerivedDirectImageCompIso Λ _ S D C p a hS₁ hD hC :=
  Functor.rightDerivedFunctorPlusChangeTarget_transportComp hC hD hS₀ hS₁
    (moduleDirectImage a Λ) (moduleDirectImage p Λ) (moduleDirectImage (a ≫ p) Λ)
    (moduleDirectImageCompIso Λ p a)

/-- The unchanged over-base comparison, including its structural equality, respects transport. -/
theorem moduleDerivedDirectImageTargetIso_over (pC : C ⟶ S) (pD : D ⟶ S)
    (a : C ⟶ D) (ha : a ≫ pD = pC) :
    Functor.isoWhiskerRight (@moduleDerivedDirectImageOverIso Λ _ S C D hS₀ hC hD
        pC pD a ha) (canonicalEquivalence hS₀ hS₁).functor ≪≫
      moduleDerivedDirectImageTargetIso Λ hC hS₀ hS₁ pC =
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hC hD
        (moduleDirectImage a Λ) _ _))
        (moduleDerivedDirectImageTargetIso Λ hD hS₀ hS₁ pD) ≪≫
      @moduleDerivedDirectImageOverIso Λ _ S C D hS₁ hC hD pC pD a ha := by
  subst pC
  simp only [moduleDerivedDirectImageOverIso, eqToIso_refl, Iso.trans_refl]
  have h := moduleDerivedDirectImageTargetIso_comp Λ hC hD hS₀ hS₁ pD a
  simpa only [← Functor.isoWhiskerRight_symm, Iso.trans_assoc,
    Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl] using
    (congrArg (fun z =>
      (Functor.isoWhiskerRight
        (@moduleDerivedDirectImageCompIso Λ _ S D C pD a hS₀ hD hC)
        (canonicalEquivalence hS₀ hS₁).functor).symm ≪≫ z ≪≫
      (@moduleDerivedDirectImageCompIso Λ _ S D C pD a hS₁ hD hC).symm) h).symm


end AlgebraicGeometry.Scheme.EtaleCohomology
