/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ChosenImageComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionSingleModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelSelf

/-!
# Choice-independent composition of exceptional direct images

The original compactified composition maps are transported to the chosen native
unbounded functors. Their actual refinement cube and an actual common
refinement prove independence of the supplied compactification tower. This file
addresses binary composition; associativity and unit coherence are separate.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wZ wF wG wFG wRaw wTop

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

variable (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  (a : F ⟶ C.first) (hRaw : HasDerivedCategory.{wRaw} (ModuleSheaf F.Xbar Λ))

omit compositeModels in
/-- The original source pair follows the actual mixed first refinement. -/
theorem moduleExceptionalUnboundedCompositionSingleSource :
    (compositionPairIso
        (moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C.first)
        (moduleExceptionalDirectImageUnboundedIso g Λ N hN hΛ C.targetCompactification)).hom ≫
      Functor.whiskerRight
        (@moduleUnboundedCompactificationMixedTransition X Y f _ Λ _ hX hY
          F C.first a hRaw (firstModels C.first))
        (moduleUnboundedCompactificationFunctor g Λ C.targetCompactification) =
    (compositionPairIso
      (moduleExceptionalUnboundedSingleValueIso f Λ N hN hΛ F hRaw)
      (moduleExceptionalUnboundedSingleValueIso g Λ N hN hΛ C.targetCompactification
        (secondModels C.targetCompactification))).hom := by
  let r := @asIso _ _ _ _
    (@moduleUnboundedCompactificationMixedTransition X Y f _ Λ _ hX hY
      F C.first a hRaw (firstModels C.first))
    (@moduleUnboundedCompactificationMixedTransition_isIso X Y f _ Λ _ hX hY
      F C.first a hRaw (firstModels C.first) N hN hΛ)
  have hf := moduleExceptionalUnboundedSingleValueIso_refinement f Λ N hN hΛ a hRaw
    (firstModels C.first)
  rw [moduleExceptionalUnboundedSingleValueIso_self] at hf
  have hi : moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C.first ≪≫ r =
      moduleExceptionalUnboundedSingleValueIso f Λ N hN hΛ F hRaw := Iso.ext hf
  rw [moduleExceptionalUnboundedSingleValueIso_self]
  exact congrArg Iso.hom (compositionPairIso_first _ _ _ r hi)

end AlgebraicGeometry.Scheme.EtaleCohomology
