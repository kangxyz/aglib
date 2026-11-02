/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperRefinementComparison
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementPullbackCoherence
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
theorem moduleUnboundedDerivedProperRefinementPullbackIso_comp :
    moduleUnboundedDerivedProperRefinementPullbackIso j₁ j₃ (a ≫ b) sq₁₃ Λ =
      Functor.isoWhiskerLeft (moduleUnboundedDerivedLowerShriek j₃ Λ)
        (moduleUnboundedDerivedInverseImageCompIso Λ b a) ≪≫
      (Functor.associator (moduleUnboundedDerivedLowerShriek j₃ Λ)
        (moduleUnboundedDerivedInverseImage Λ b) (moduleUnboundedDerivedInverseImage Λ a)).symm ≪≫
      Functor.isoWhiskerRight (moduleUnboundedDerivedProperRefinementPullbackIso j₂ j₃ b sq₂₃ Λ)
        (moduleUnboundedDerivedInverseImage Λ a) ≪≫
      moduleUnboundedDerivedProperRefinementPullbackIso j₁ j₂ a sq₁₂ Λ := by
  exact Functor.mapDerivedCategoryTriangleIso_comp
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
theorem moduleUnboundedDerivedProperRefinementComparison_comp :
    moduleUnboundedDerivedProperRefinementComparison j₁ j₃ (a ≫ b) sq₁₃ Λ ≫
      Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek j₁ Λ)
        (moduleUnboundedDerivedDirectImageCompIso Λ b a).hom =
    moduleUnboundedDerivedProperRefinementComparison j₂ j₃ b sq₂₃ Λ ≫
      Functor.whiskerRight (moduleUnboundedDerivedProperRefinementComparison j₁ j₂ a sq₁₂ Λ)
        (moduleUnboundedDerivedDirectImage Λ b) ≫
      (Functor.associator (moduleUnboundedDerivedLowerShriek j₁ Λ)
        (moduleUnboundedDerivedDirectImage Λ a) (moduleUnboundedDerivedDirectImage Λ b)).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id,
    moduleUnboundedDerivedProperRefinementComparison_app]
  exact adjunctionUnitComparison_comp
    (moduleUnboundedDerivedAdjunction Λ b) (moduleUnboundedDerivedAdjunction Λ a)
    (moduleUnboundedDerivedAdjunction Λ (a ≫ b))
    (moduleUnboundedDerivedProperRefinementPullbackIso j₂ j₃ b sq₂₃ Λ)
    (moduleUnboundedDerivedProperRefinementPullbackIso j₁ j₂ a sq₁₂ Λ)
    (moduleUnboundedDerivedProperRefinementPullbackIso j₁ j₃ (a ≫ b) sq₁₃ Λ)
    (moduleUnboundedDerivedInverseImageCompIso Λ b a)
    (moduleUnboundedDerivedDirectImageCompIso Λ b a)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageCompIso_hom Λ b a)
    (moduleUnboundedDerivedProperRefinementPullbackIso_comp j₁ j₂ j₃ a b sq₁₂ sq₂₃ sq₁₃ Λ) K

end AlgebraicGeometry.Scheme.EtaleCohomology
