/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LeftUnitSuppliedIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelSelf
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelArrow
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Composition
public import Aglib.CategoryTheory.Functor.ChosenLeftUnit

/-! # Descent of the proved left-unit triangle through the original canonical comparisons

The identity contraction is still expressed through one endpoint-modeled
identity value. Its identification with the original independently modeled
chosen epsilon is a separate original mixed-identity normalization.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wA wB wD
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [IsSeparated f] [LocallyOfFiniteType f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [firstModels : ∀ E : Hom.DenseCompactification (𝟙 X),
    HasDerivedCategory.{wA} (ModuleSheaf E.Xbar Λ)]
  [targetModels : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wD} (ModuleSheaf E.Xbar Λ)]
  [compositeModels : ∀ E : Hom.DenseCompactification ((𝟙 X) ≫ f),
    HasDerivedCategory.{wB} (ModuleSheaf E.Xbar Λ)]
  (C : Hom.DenseCompactification f)

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

include C in
/-- The original chosen compositor contracts through the original single-value comparison. -/
theorem moduleExceptionalUnboundedLeftUnitContraction :
    moduleExceptionalDirectImageUnboundedCompIso (𝟙 X) f Λ N hN hΛ ≪≫
      moduleExceptionalDirectImageUnboundedCongr Λ hX hY (Category.id_comp f)
        compositeModels targetModels N hN hΛ =
    Functor.isoWhiskerRight
        (moduleExceptionalUnboundedSingleValueIso (hX := hX) (hS := hX)
            (models := firstModels) (𝟙 X) Λ N hN hΛ (Hom.DenseCompactification.ofProper (𝟙 X)) hX ≪≫
          moduleUnboundedSingleIdentityValueIso (hX := hX) (hM := hX) X Λ)
        (moduleExceptionalDirectImageUnbounded f Λ) ≪≫
      Functor.leftUnitor (moduleExceptionalDirectImageUnbounded f Λ) := by
  apply chosenLeftUnit
    (χQ := moduleExceptionalDirectImageUnboundedIso (𝟙 X) Λ N hN hΛ
      (Hom.CompactifiedComposition.leftUnit C).first)
    (χF := moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C)
    (χH := moduleExceptionalDirectImageUnboundedIso ((𝟙 X) ≫ f) Λ N hN hΛ
      (Hom.CompactifiedComposition.leftUnit C).composite)
    (τ := moduleUnboundedLeftUnitFirstIso f Λ C N hN hΛ)
    (α := moduleUnboundedCompactifiedCompositionIso (𝟙 X) f Λ
      (Hom.CompactifiedComposition.leftUnit C) N hN hΛ)
    (t := moduleUnboundedLeftUnitTotalIso f Λ C N hN hΛ)
  · have hs := moduleExceptionalUnboundedSingleValueIso_refinementIso (𝟙 X) Λ
      (Hom.CompactifiedComposition.leftUnitFirstRefinement C)
      (firstModels (Hom.CompactifiedComposition.leftUnit C).first) hX N hN hΛ
    exact hs.trans (moduleExceptionalUnboundedSingleValueIso_self (𝟙 X) Λ N hN hΛ
      (Hom.CompactifiedComposition.leftUnit C).first)
  · exact (moduleExceptionalDirectImageUnboundedCompIso_comparison (𝟙 X) f Λ N hN hΛ
      (Hom.CompactifiedComposition.leftUnit C)).symm
  · exact moduleUnboundedLeftUnitSuppliedIso f Λ C N hN hΛ
  · have ht := moduleExceptionalUnboundedSingleValueIso_refinementIso f Λ
      (Hom.CompactifiedComposition.leftUnitTotalRefinement C)
      (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite) (targetModels C) N hN hΛ
    have hc := moduleExceptionalUnboundedSingleValueIso_self f Λ N hN hΛ C
    have ht' := (congrArg (fun z => z ≪≫ moduleUnboundedLeftUnitTotalIso f Λ C N hN hΛ)
      hc).symm.trans ht
    have hg := moduleExceptionalUnboundedSingleValueIso_congr Λ hX hY (Category.id_comp f)
      compositeModels targetModels N hN hΛ (Hom.CompactifiedComposition.leftUnit C).composite
      (compositeModels (Hom.CompactifiedComposition.leftUnit C).composite)
    have htotal := congrArg
      (fun z => moduleExceptionalDirectImageUnboundedCongr Λ hX hY (Category.id_comp f)
        compositeModels targetModels N hN hΛ ≪≫ z) ht'
    exact htotal.trans (hg.trans
      (moduleExceptionalUnboundedSingleValueIso_self ((𝟙 X) ≫ f) Λ N hN hΛ
        (Hom.CompactifiedComposition.leftUnit C).composite))

end AlgebraicGeometry.Scheme.EtaleCohomology
