/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelComparison

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
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

variable (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  (hRaw : HasDerivedCategory.{wRaw} (ModuleSheaf F.Xbar Λ))
  (hTop : HasDerivedCategory.{wTop} (ModuleSheaf C.composite.Xbar Λ))

/-- The original chosen compositor transported by original single-value comparisons.
Its equality to the actual Cartesian map is a separate proved normalization. -/
def moduleExceptionalUnboundedCompositionSingleModelIso :
    @moduleUnboundedCompactificationFunctor X Y f Λ _ _ _ F hRaw ⋙
        @moduleUnboundedCompactificationFunctor Y Z g Λ _ _ _ C.targetCompactification
          (secondModels C.targetCompactification) ≅
      @moduleUnboundedCompactificationFunctor X Z (f ≫ g) Λ _ _ _ C.composite hTop :=
  (compositionPairIso
    (moduleExceptionalUnboundedSingleValueIso f Λ N hN hΛ F hRaw)
    (moduleExceptionalUnboundedSingleValueIso g Λ N hN hΛ C.targetCompactification
      (secondModels C.targetCompactification))).symm ≪≫
    moduleExceptionalDirectImageUnboundedCompIso f g Λ N hN hΛ ≪≫
    moduleExceptionalUnboundedSingleValueIso (f ≫ g) Λ N hN hΛ C.composite hTop

/-- The native comparison square retains the original chosen compositor and comparisons. -/
theorem moduleExceptionalUnboundedCompositionSingleModelIso_comparison :
    compositionPairIso
        (moduleExceptionalUnboundedSingleValueIso f Λ N hN hΛ F hRaw)
        (moduleExceptionalUnboundedSingleValueIso g Λ N hN hΛ C.targetCompactification
          (secondModels C.targetCompactification)) ≪≫
      moduleExceptionalUnboundedCompositionSingleModelIso f g Λ N hN hΛ C F hRaw hTop =
    moduleExceptionalDirectImageUnboundedCompIso f g Λ N hN hΛ ≪≫
      moduleExceptionalUnboundedSingleValueIso (f ≫ g) Λ N hN hΛ C.composite hTop := by
  simp only [moduleExceptionalUnboundedCompositionSingleModelIso, Iso.self_symm_id_assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology
