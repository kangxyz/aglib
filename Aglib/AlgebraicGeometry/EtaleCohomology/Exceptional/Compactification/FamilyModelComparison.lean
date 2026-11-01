/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ModelComparisonCoherence

/-! # Coherent comparison of independent compactification model families

The comparator is the original transition of the geometric identity, with its
two middle models retained independently. Its orientation is from the first
family to the second. It is not identified with a different localization-based
comparison without an additional proof.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM₀ wM₁ wM₂
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))
  (models₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ))
  (models₁ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ))

/-- The original refinement map from the first family to the second family. -/
def moduleCompactificationFamilyTransition {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    (@moduleCompactificationFunctor X S f Λ _ hX hS D (models₀ D)) ⟶
      (@moduleCompactificationFunctor X S f Λ _ hX hS C (models₁ C)) :=
  @moduleCompactificationMixedTransition X S f _ Λ _ hX hS C D a (models₁ C) (models₀ D)

instance moduleCompactificationFamilyTransition_isIso
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    IsIso (moduleCompactificationFamilyTransition f Λ hX hS models₀ models₁ a) :=
  @moduleCompactificationMixedTransition_isIso X S f _ Λ _ hX hS C D a
    (models₁ C) (models₀ D)

/-- The original mixed identity refinement, from the first family to the second. -/
def moduleCompactificationFamilyComparison (C : Hom.DenseCompactification f) :
    (@moduleCompactificationFunctor X S f Λ _ hX hS C (models₀ C)) ≅
      (@moduleCompactificationFunctor X S f Λ _ hX hS C (models₁ C)) :=
  asIso (moduleCompactificationFamilyTransition f Λ hX hS models₀ models₁ (𝟙 C))

/-- Literal original identity-refinement components, including the proper-image compositor. -/
theorem moduleCompactificationFamilyComparison_hom_app (C : Hom.DenseCompactification f)
    (K : (@moduleTorsionCohomologyPlus X Λ _ hX).FullSubcategory) :
    (moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ C).hom.app K =
      (@Functor.rightDerivedFunctorPlus (ModuleSheaf C.Xbar Λ) (ModuleSheaf S Λ)
        _ _ _ _ (models₀ C) hS (moduleDirectImage C.p Λ) _ _).map
        ((@moduleDerivedRefinementComparison X S f _ C C (𝟙 C) Λ _
          hX (models₁ C) (models₀ C)).app K.obj) ≫
        (@moduleDerivedRefinementDirectImageIso Λ _ X S f hS C C (𝟙 C)
          (models₁ C) (models₀ C)).hom.app
          ((@moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (models₁ C)).obj K.obj) :=
  imageComparison_app _ _ K.obj

variable (models₂ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₂} (ModuleSheaf C.Xbar Λ))

/-- Mixed family transitions compose with their original maps. -/
theorem moduleCompactificationFamilyTransition_comp
    {C D E : Hom.DenseCompactification f} (a : C ⟶ D) (b : D ⟶ E) :
    moduleCompactificationFamilyTransition f Λ hX hS models₀ models₂ (a ≫ b) =
      moduleCompactificationFamilyTransition f Λ hX hS models₀ models₁ b ≫
        moduleCompactificationFamilyTransition f Λ hX hS models₁ models₂ a :=
  @moduleCompactificationMixedTransition_comp X S f _ Λ _ hX hS C D a
    (models₂ C) (models₁ D) E b (models₀ E)

/-- Original refinement arrows commute with the mixed identity-family comparison. -/
theorem moduleCompactificationFamilyComparison_naturality
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    moduleCompactificationFamilyTransition f Λ hX hS models₀ models₀ a ≫
        (moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ C).hom =
      (moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ D).hom ≫
        moduleCompactificationFamilyTransition f Λ hX hS models₁ models₁ a := by
  have h₀ := moduleCompactificationFamilyTransition_comp f Λ hX hS
    models₀ models₀ models₁ (𝟙 C) a
  have h₁ := moduleCompactificationFamilyTransition_comp f Λ hX hS
    models₀ models₁ models₁ a (𝟙 D)
  simp only [Category.id_comp, Category.comp_id] at h₀ h₁
  change moduleCompactificationFamilyTransition f Λ hX hS models₀ models₀ a ≫
      moduleCompactificationFamilyTransition f Λ hX hS models₀ models₁ (𝟙 C) =
    moduleCompactificationFamilyTransition f Λ hX hS models₀ models₁ (𝟙 D) ≫
      moduleCompactificationFamilyTransition f Λ hX hS models₁ models₁ a
  exact h₀.symm.trans h₁

/-- The canonical mixed identity comparisons satisfy the actual family cocycle. -/
theorem moduleCompactificationFamilyComparison_trans (C : Hom.DenseCompactification f) :
    moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ C ≪≫
        moduleCompactificationFamilyComparison f Λ hX hS models₁ models₂ C =
      moduleCompactificationFamilyComparison f Λ hX hS models₀ models₂ C := by
  apply Iso.ext
  change moduleCompactificationFamilyTransition f Λ hX hS models₀ models₁ (𝟙 C) ≫
      moduleCompactificationFamilyTransition f Λ hX hS models₁ models₂ (𝟙 C) =
    moduleCompactificationFamilyTransition f Λ hX hS models₀ models₂ (𝟙 C)
  simpa only [Category.id_comp] using
    (moduleCompactificationFamilyTransition_comp f Λ hX hS
      models₀ models₁ models₂ (𝟙 C) (𝟙 C)).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
