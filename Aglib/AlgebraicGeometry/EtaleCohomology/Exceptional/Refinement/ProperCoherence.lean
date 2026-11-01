/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.ProperComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.PullbackCoherence
public import Aglib.CategoryTheory.Adjunction.UnitComparisonCoherence

/-!
# Composition of original comparisons for arbitrary Cartesian open refinements

The same original pullback comparisons and derived units satisfy composition
without any density assumption. The proof specializes the existing abstract
exact-functor and adjunction coherence; it does not choose replacement maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u w w₁ w₂ w₃

variable {X Y₁ Y₂ Y₃ : Scheme.{u}}
  (j₁ : X ⟶ Y₁) (j₂ : X ⟶ Y₂) (j₃ : X ⟶ Y₃)
  [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
  (a : Y₁ ⟶ Y₂) (b : Y₂ ⟶ Y₃)
  (sq₁₂ : IsPullback j₁ (𝟙 X) a j₂)
  (sq₂₃ : IsPullback j₂ (𝟙 X) b j₃)
  (sq₁₃ : IsPullback j₁ (𝟙 X) (a ≫ b) j₃)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{w₁} (ModuleSheaf Y₁ Λ)]
  [HasDerivedCategory.{w₂} (ModuleSheaf Y₂ Λ)]
  [HasDerivedCategory.{w₃} (ModuleSheaf Y₃ Λ)]

/-- Original open pullback comparisons compose before any density restriction. -/
theorem moduleDerivedProperRefinementPullbackIso_comp :
    moduleDerivedProperRefinementPullbackIso j₁ j₃ (a ≫ b) sq₁₃ Λ =
      Functor.isoWhiskerLeft (moduleDerivedLowerShriek j₃ Λ)
        (moduleDerivedInverseImageCompIso Λ b a) ≪≫
      (Functor.associator (moduleDerivedLowerShriek j₃ Λ)
        (moduleDerivedInverseImage Λ b) (moduleDerivedInverseImage Λ a)).symm ≪≫
      Functor.isoWhiskerRight (moduleDerivedProperRefinementPullbackIso j₂ j₃ b sq₂₃ Λ)
        (moduleDerivedInverseImage Λ a) ≪≫
      moduleDerivedProperRefinementPullbackIso j₁ j₂ a sq₁₂ Λ := by
  exact Functor.rightDerivedFunctorPlusPullbackIso_comp
    (moduleLowerShriek j₃ Λ) (moduleInverseImage b Λ) (moduleInverseImage a Λ)
    (moduleLowerShriek j₂ Λ) (moduleInverseImage (a ≫ b) Λ) (moduleLowerShriek j₁ Λ)
    (moduleLowerShriekCartesianIdentityIso j₂ j₃ b sq₂₃.flip Λ)
    (moduleLowerShriekCartesianIdentityIso j₁ j₂ a sq₁₂.flip Λ)
    (moduleLowerShriekCartesianIdentityIso j₁ j₃ (a ≫ b) sq₁₃.flip Λ)
    (moduleInverseImageCompIso Λ b a)
    (moduleLowerShriekCartesianIdentityIso_comp j₁ j₂ j₃ b a
      sq₂₃.flip sq₁₂.flip sq₁₃.flip Λ)

/-- Composition of the same original derived-unit comparisons for arbitrary
Cartesian open refinements. Properness is unnecessary for this equality. -/
theorem moduleDerivedProperRefinementComparison_comp :
    moduleDerivedProperRefinementComparison j₁ j₃ (a ≫ b) sq₁₃ Λ ≫
      Functor.whiskerLeft (moduleDerivedLowerShriek j₁ Λ)
        (moduleDerivedDirectImageCompIso Λ b a).hom =
    moduleDerivedProperRefinementComparison j₂ j₃ b sq₂₃ Λ ≫
      Functor.whiskerRight (moduleDerivedProperRefinementComparison j₁ j₂ a sq₁₂ Λ)
        (moduleDerivedDirectImage Λ b) ≫
      (Functor.associator (moduleDerivedLowerShriek j₁ Λ)
        (moduleDerivedDirectImage Λ a) (moduleDerivedDirectImage Λ b)).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id, moduleDerivedProperRefinementComparison_app]
  exact adjunctionUnitComparison_comp
    (moduleDerivedAdjunction Λ b) (moduleDerivedAdjunction Λ a)
    (moduleDerivedAdjunction Λ (a ≫ b))
    (moduleDerivedProperRefinementPullbackIso j₂ j₃ b sq₂₃ Λ)
    (moduleDerivedProperRefinementPullbackIso j₁ j₂ a sq₁₂ Λ)
    (moduleDerivedProperRefinementPullbackIso j₁ j₃ (a ≫ b) sq₁₃ Λ)
    (moduleDerivedInverseImageCompIso Λ b a)
    (moduleDerivedDirectImageCompIso Λ b a)
    (conjugateEquiv_moduleDerivedInverseImageCompIso_hom Λ b a)
    (moduleDerivedProperRefinementPullbackIso_comp j₁ j₂ j₃ a b sq₁₂ sq₂₃ sq₁₃ Λ) K

end AlgebraicGeometry.Scheme.EtaleCohomology
