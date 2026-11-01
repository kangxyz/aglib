/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModelComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelFamily
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionFamilyComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ArrowComparisonCoherence

/-! # Original arrow equality preserves the chosen unbounded compositor -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wF₀ wF₁ wG₀ wG₁ wH₀ wH₁

variable {X Y Z : Scheme.{u}} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
  [QuasiCompact f] [QuasiCompact g] [QuasiCompact f'] [QuasiCompact g'] (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  (F₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF₀} (ModuleSheaf C.Xbar Λ))
  (F₁ : ∀ C : Hom.DenseCompactification f',
    HasDerivedCategory.{wF₁} (ModuleSheaf C.Xbar Λ))
  (G₀ : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG₀} (ModuleSheaf C.Xbar Λ))
  (G₁ : ∀ C : Hom.DenseCompactification g',
    HasDerivedCategory.{wG₁} (ModuleSheaf C.Xbar Λ))
  (H₀ : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wH₀} (ModuleSheaf C.Xbar Λ))
  (H₁ : ∀ C : Hom.DenseCompactification (f' ≫ g'),
    HasDerivedCategory.{wH₁} (ModuleSheaf C.Xbar Λ))

variable [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  [IsSeparated f'] [LocallyOfFiniteType f'] [IsSeparated g'] [LocallyOfFiniteType g']

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Only original arrow equalities and original family maps transport the compositor. -/
theorem moduleExceptionalDirectImageUnboundedCompIso_congr
    (ef : f = f') (eg : g = g') (efg : f ≫ g = f' ≫ g') :
    compositionPairIso
        (moduleExceptionalDirectImageUnboundedCongr Λ hX hY ef F₀ F₁ N hN hΛ)
        (moduleExceptionalDirectImageUnboundedCongr Λ hY hZ eg G₀ G₁ N hN hΛ) ≪≫
      moduleExceptionalDirectImageUnboundedCompIso (firstModels := F₁)
        (secondModels := G₁) (compositeModels := H₁) f' g' Λ N hN hΛ =
    moduleExceptionalDirectImageUnboundedCompIso (firstModels := F₀)
        (secondModels := G₀) (compositeModels := H₀) f g Λ N hN hΛ ≪≫
      moduleExceptionalDirectImageUnboundedCongr Λ hX hZ efg H₀ H₁ N hN hΛ := by
  subst f'
  subst g'
  exact moduleExceptionalDirectImageUnboundedCompIso_familyComparison f g Λ
    F₀ F₁ G₀ G₁ H₀ H₁ N hN hΛ

end AlgebraicGeometry.Scheme.EtaleCohomology
