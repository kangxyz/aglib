/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModelComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelFamily
public import Aglib.CategoryTheory.Functor.CompositionFamilySquare

/-! # The original chosen unbounded compositor respects six independent model families -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wF₀ wF₁ wG₀ wG₁ wH₀ wH₁

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g] (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  (F₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF₀} (ModuleSheaf C.Xbar Λ))
  (F₁ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF₁} (ModuleSheaf C.Xbar Λ))
  (G₀ : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG₀} (ModuleSheaf C.Xbar Λ))
  (G₁ : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG₁} (ModuleSheaf C.Xbar Λ))
  (H₀ : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wH₀} (ModuleSheaf C.Xbar Λ))
  (H₁ : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wH₁} (ModuleSheaf C.Xbar Λ))

variable [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The actual original six-family model square descends to the chosen compositor. -/
theorem moduleExceptionalDirectImageUnboundedCompIso_familyComparison :
    compositionPairIso
        (moduleExceptionalDirectImageUnboundedFamilyComparison f Λ hX hY F₀ F₁ N hN hΛ)
        (moduleExceptionalDirectImageUnboundedFamilyComparison g Λ hY hZ G₀ G₁ N hN hΛ) ≪≫
      moduleExceptionalDirectImageUnboundedCompIso (firstModels := F₁)
        (secondModels := G₁) (compositeModels := H₁) f g Λ N hN hΛ =
    moduleExceptionalDirectImageUnboundedCompIso (firstModels := F₀)
        (secondModels := G₀) (compositeModels := H₀) f g Λ N hN hΛ ≪≫
      moduleExceptionalDirectImageUnboundedFamilyComparison (f ≫ g) Λ hX hZ H₀ H₁ N hN hΛ := by
  let C : Hom.CompactifiedComposition f g := Classical.choice inferInstance
  apply compositionFamilySquare
    _ _ _
    (moduleExceptionalDirectImageUnboundedIso (middleModels := F₀) f Λ N hN hΛ C.first)
    (moduleExceptionalDirectImageUnboundedIso (middleModels := F₁) f Λ N hN hΛ C.first)
    (moduleExceptionalDirectImageUnboundedIso (middleModels := G₀) g Λ N hN hΛ
      C.targetCompactification)
    (moduleExceptionalDirectImageUnboundedIso (middleModels := G₁) g Λ N hN hΛ
      C.targetCompactification)
    (moduleExceptionalDirectImageUnboundedIso (middleModels := H₀) (f ≫ g) Λ N hN hΛ C.composite)
    (moduleExceptionalDirectImageUnboundedIso (middleModels := H₁) (f ≫ g) Λ N hN hΛ C.composite)
    (moduleUnboundedCompactificationFamilyComparison f Λ hX hY F₀ F₁ N hN hΛ C.first)
    (moduleUnboundedCompactificationFamilyComparison g Λ hY hZ G₀ G₁ N hN hΛ
      C.targetCompactification)
    (moduleUnboundedCompactificationFamilyComparison (f ≫ g) Λ hX hZ H₀ H₁ N hN hΛ C.composite)
    _ _
    (moduleUnboundedCompactifiedCompositionIso (firstModels := F₀) (secondModels := G₀)
      (compositeModels := H₀) f g Λ C N hN hΛ)
    (moduleUnboundedCompactifiedCompositionIso (firstModels := F₁) (secondModels := G₁)
      (compositeModels := H₁) f g Λ C N hN hΛ)
  · exact moduleUnboundedCompactificationFamilyComparison_canonical f Λ hX hY F₀ F₁
      N hN hΛ (moduleExceptionalCompactification f) C.first
  · exact moduleUnboundedCompactificationFamilyComparison_canonical g Λ hY hZ G₀ G₁
      N hN hΛ (moduleExceptionalCompactification g) C.targetCompactification
  · exact moduleUnboundedCompactificationFamilyComparison_canonical (f ≫ g) Λ hX hZ H₀ H₁
      N hN hΛ (moduleExceptionalCompactification (f ≫ g)) C.composite
  · exact moduleExceptionalDirectImageUnboundedCompIso_comparison
      (firstModels := F₀) (secondModels := G₀) (compositeModels := H₀) f g Λ N hN hΛ C
  · exact moduleExceptionalDirectImageUnboundedCompIso_comparison
      (firstModels := F₁) (secondModels := G₁) (compositeModels := H₁) f g Λ N hN hΛ C
  · exact moduleUnboundedCompactifiedCompositionIso_familyComparison f g Λ
      F₀ F₁ G₀ G₁ H₀ H₁ C N hN hΛ

end AlgebraicGeometry.Scheme.EtaleCohomology
