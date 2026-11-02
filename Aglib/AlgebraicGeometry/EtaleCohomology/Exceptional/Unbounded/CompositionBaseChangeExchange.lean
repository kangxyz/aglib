/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Pasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangePasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenComparisonPasting

/-! # Original compactified exchange for a commuting proper face

Open faces are Cartesian. Proper faces only commute, allowing the actual
normalization refinement of a base-changed compactification. No invertibility
claim is attached to these maps. Their restriction recovers original Cartesian
base change literally.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wM wS wU' wM' wS'

section Map
variable {U M S U' M' S' : Scheme.{u}}
  (j : U ⟶ M) (p : M ⟶ S) (j' : U' ⟶ M') (p' : M' ⟶ S')
  (a : U' ⟶ U) (q : M' ⟶ M) (b : S' ⟶ S)
  [IsOpenImmersion j] [IsOpenImmersion j']
  (hj : IsPullback a j' j q) (hp : p' ≫ b = q ≫ p)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf M Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wU'} (ModuleSheaf U' Λ)]
  [HasDerivedCategory.{wM'} (ModuleSheaf M' Λ)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]

/-- The same original proper exchange and open comparison for a commuting
proper face. Invertibility is a separate mathematical assertion. -/
def moduleUnboundedCompactifiedCommutingExchange :
    (moduleUnboundedDerivedLowerShriek j Λ ⋙ moduleUnboundedDerivedDirectImage Λ p) ⋙
        moduleUnboundedDerivedInverseImage Λ b ⟶
      moduleUnboundedDerivedInverseImage Λ a ⋙
        (moduleUnboundedDerivedLowerShriek j' Λ ⋙ moduleUnboundedDerivedDirectImage Λ p') :=
  compositeExchange (moduleUnboundedDerivedBaseChangeMap Λ p p' b q hp)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j' j q hj Λ)

/-- On an actual Cartesian proper face this is the exact original base-change map. -/
theorem moduleUnboundedCompactifiedCommutingExchange_cartesian (sq : IsPullback q p' p b) :
    moduleUnboundedCompactifiedCommutingExchange j p j' p' a q b hj sq.w.symm Λ =
      moduleUnboundedCompactifiedBaseChangeMap j p j' p' a q b hj sq Λ := rfl

end Map

universe wU₀ wM₀ wS₀ wU₁ wM₁ wS₁ wU₂ wM₂ wS₂

variable {U₀ M₀ S₀ U₁ M₁ S₁ U₂ M₂ S₂ : Scheme.{u}}
  (j₀ : U₀ ⟶ M₀) (p₀ : M₀ ⟶ S₀)
  (j₁ : U₁ ⟶ M₁) (p₁ : M₁ ⟶ S₁)
  (j₂ : U₂ ⟶ M₂) (p₂ : M₂ ⟶ S₂)
  (a₁ : U₁ ⟶ U₀) (c₁ : M₁ ⟶ M₀) (b₁ : S₁ ⟶ S₀)
  (a₂ : U₂ ⟶ U₁) (c₂ : M₂ ⟶ M₁) (b₂ : S₂ ⟶ S₁)
  [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
  (hj₁ : IsPullback a₁ j₁ j₀ c₁) (hp₁ : p₁ ≫ b₁ = c₁ ≫ p₀)
  (hj₂ : IsPullback a₂ j₂ j₁ c₂) (hp₂ : p₂ ≫ b₂ = c₂ ≫ p₁)
  (hj : IsPullback (a₂ ≫ a₁) j₂ j₀ (c₂ ≫ c₁))
  (hp : p₂ ≫ (b₂ ≫ b₁) = (c₂ ≫ c₁) ≫ p₀)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
  [HasDerivedCategory.{wM₀} (ModuleSheaf M₀ Λ)]
  [HasDerivedCategory.{wS₀} (ModuleSheaf S₀ Λ)]
  [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
  [HasDerivedCategory.{wM₁} (ModuleSheaf M₁ Λ)]
  [HasDerivedCategory.{wS₁} (ModuleSheaf S₁ Λ)]
  [HasDerivedCategory.{wU₂} (ModuleSheaf U₂ Λ)]
  [HasDerivedCategory.{wM₂} (ModuleSheaf M₂ Λ)]
  [HasDerivedCategory.{wS₂} (ModuleSheaf S₂ Λ)]

/-- Actual consecutive base change of the proper/open compactified map,
retained as the original whole equation on the nine independent models. -/
theorem moduleUnboundedCompactifiedCommutingExchange_pasting
    (K : DerivedCategory (ModuleSheaf U₀ Λ)) :
    ActualHorizontalMateEquation
      (moduleUnboundedCompactifiedCommutingExchange j₀ p₀ j₁ p₁ a₁ c₁ b₁ hj₁ hp₁ Λ)
      (moduleUnboundedCompactifiedCommutingExchange j₁ p₁ j₂ p₂ a₂ c₂ b₂ hj₂ hp₂ Λ)
      (moduleUnboundedCompactifiedCommutingExchange j₀ p₀ j₂ p₂
        (a₂ ≫ a₁) (c₂ ≫ c₁) (b₂ ≫ b₁) hj hp Λ)
      (moduleUnboundedDerivedInverseImageCompIso Λ b₁ b₂).hom
      (moduleUnboundedDerivedInverseImageCompIso Λ a₁ a₂).hom K :=
  compositeExchange_pasting_of_equations
    (moduleUnboundedDerivedBaseChangeMap Λ p₀ p₁ b₁ c₁ hp₁)
    (moduleUnboundedDerivedBaseChangeMap Λ p₁ p₂ b₂ c₂ hp₂)
    (moduleUnboundedDerivedBaseChangeMap Λ p₀ p₂ (b₂ ≫ b₁) (c₂ ≫ c₁) hp)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a₁ j₁ j₀ c₁ hj₁ Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a₂ j₂ j₁ c₂ hj₂ Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (a₂ ≫ a₁) j₂ j₀ (c₂ ≫ c₁) hj Λ)
    (moduleUnboundedDerivedInverseImageCompIso Λ b₁ b₂)
    (moduleUnboundedDerivedInverseImageCompIso Λ c₁ c₂)
    (moduleUnboundedDerivedInverseImageCompIso Λ a₁ a₂)
    (moduleUnboundedCompactifiedCommutingExchange j₀ p₀ j₁ p₁ a₁ c₁ b₁ hj₁ hp₁ Λ)
    (moduleUnboundedCompactifiedCommutingExchange j₁ p₁ j₂ p₂ a₂ c₂ b₂ hj₂ hp₂ Λ)
    (moduleUnboundedCompactifiedCommutingExchange j₀ p₀ j₂ p₂
      (a₂ ≫ a₁) (c₂ ≫ c₁) (b₂ ≫ b₁) hj hp Λ)
    rfl rfl rfl
    (moduleUnboundedDerivedBaseChangeMap_hComp Λ p₀ p₁ p₂ b₁ b₂ c₁ c₂
      hp₁ hp₂ hp)
    (moduleUnboundedDerivedOpenComparison_pasting j₀ j₁ j₂ a₁ a₂ c₁ c₂ hj₁ hj₂ hj Λ) K

end AlgebraicGeometry.Scheme.EtaleCohomology
