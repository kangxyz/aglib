/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.FamilyModelComparison

/-! # Original scheme-arrow equality and coherent exceptional model-family transport

Equality transport uses only the original equality of scheme morphisms. The
subsequent family comparison is the original mixed identity-refinement map;
it is not defined using the exceptional compositor or a new chosen isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM₀ wM₁

variable {X S : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
  {f g : X ⟶ S}

/-- Reindex the actual middle-model family along the original equality of arrows. -/
abbrev moduleCompactificationModelFamilyCongr (e : f = g)
    (models : ∀ C : Hom.DenseCompactification f,
      HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ)) :
    ∀ C : Hom.DenseCompactification g,
      HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ) := by
  subst g
  exact models

variable [CompactSpace S] [QuasiSeparatedSpace S]
  [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact g] [IsSeparated g] [LocallyOfFiniteType g]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ))

/-- Literal equality transport of the chosen native functor, retaining its transported family. -/
def moduleExceptionalDirectImagePlusTorsionArrowIso (e : f = g)
    (models : ∀ C : Hom.DenseCompactification f,
      HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ)) :
    (@moduleExceptionalDirectImagePlusTorsion X S f _ Λ _ hX hS
      _ _ _ _ (models (moduleExceptionalCompactification f))) ≅
      (@moduleExceptionalDirectImagePlusTorsion X S g _ Λ _ hX hS _ _ _ _
        (moduleCompactificationModelFamilyCongr Λ e models
          (moduleExceptionalCompactification g))) := by
  subst g
  exact Iso.refl _

/-- Normalize equal scheme arrows with fully independent original middle families. -/
def moduleExceptionalDirectImagePlusTorsionCongr (e : f = g)
    (models₀ : ∀ C : Hom.DenseCompactification f,
      HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ))
    (models₁ : ∀ C : Hom.DenseCompactification g,
      HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ)) :
    (@moduleExceptionalDirectImagePlusTorsion X S f _ Λ _ hX hS
      _ _ _ _ (models₀ (moduleExceptionalCompactification f))) ≅
      (@moduleExceptionalDirectImagePlusTorsion X S g _ Λ _ hX hS
      _ _ _ _ (models₁ (moduleExceptionalCompactification g))) :=
  moduleExceptionalDirectImagePlusTorsionArrowIso Λ hX hS e models₀ ≪≫
    moduleExceptionalDirectImagePlusTorsionFamilyComparison g Λ hX hS
      (moduleCompactificationModelFamilyCongr Λ e models₀) models₁

/-- At literal equality this is exactly the original coherent family comparison. -/
theorem moduleExceptionalDirectImagePlusTorsionCongr_refl
    (models₀ : ∀ C : Hom.DenseCompactification f,
      HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ))
    (models₁ : ∀ C : Hom.DenseCompactification f,
      HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ)) :
    moduleExceptionalDirectImagePlusTorsionCongr Λ hX hS (rfl : f = f) models₀ models₁ =
      moduleExceptionalDirectImagePlusTorsionFamilyComparison f Λ hX hS models₀ models₁ := by
  simp only [moduleExceptionalDirectImagePlusTorsionCongr,
    moduleExceptionalDirectImagePlusTorsionArrowIso, moduleCompactificationModelFamilyCongr,
    Iso.refl_trans]

end AlgebraicGeometry.Scheme.EtaleCohomology
