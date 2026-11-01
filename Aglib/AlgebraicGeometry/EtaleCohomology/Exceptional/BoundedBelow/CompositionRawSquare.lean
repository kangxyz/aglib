/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionSingleSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianFirstTargetComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianCompositionCanonical

/-!
# Choice-independent composition of exceptional direct images

The original compactified composition maps are transported to the chosen native
bounded-below torsion functors. Their actual refinement cube and an actual common
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

variable (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  (hRaw : HasDerivedCategory.{wRaw} (ModuleSheaf F.Xbar Λ))
  (hTop : HasDerivedCategory.{wTop} (ModuleSheaf C.composite.Xbar Λ))

variable (m : F.Xbar ⟶ C.sourceCompactification.Xbar) [IsOpenImmersion m]
  (sq : IsPullback m F.p C.sourceCompactification.p C.targetCompactification.j)
  (a : F ⟶ C.first)
  (sqMid : IsPullback m a.hom (𝟙 C.sourceCompactification.Xbar) C.middleOpen)
  (hj : F.j ≫ m = C.sourceCompactification.j)
  (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory)

include sqMid in
/-- The original chosen compositor and the actual Cartesian map form the same component square. -/
theorem moduleExceptionalCompositionRawSquare :
    ChosenImageSquareEquation
      (((compositionPairIso
        (moduleExceptionalSingleTorsionValueIso f Λ F hRaw)
        (moduleExceptionalSingleTorsionValueIso g Λ C.targetCompactification
          (secondModels C.targetCompactification))).hom.app K).hom)
      ((moduleCartesianCompositionMap C F m sq hj Λ hX hY hZ hRaw
        (secondModels C.targetCompactification) hTop).app K)
      (((moduleExceptionalCompositionIso f g Λ).hom.app K).hom)
      (((moduleExceptionalSingleTorsionValueIso (f ≫ g) Λ C.composite hTop).hom.app K).hom) := by
  have hk := congrArg (fun e => (e.hom.app K).hom)
    (moduleExceptionalCompositionIso_comparison f g Λ C)
  have hs := congrArg (fun e => (e.hom.app K).hom)
    (moduleExceptionalCompositionSingleSource f g Λ C F a hRaw)
  have ht :
      ((moduleExceptionalDirectImagePlusTorsionIso (f ≫ g) Λ C.composite).hom.app K).hom ≫
        (@moduleCompactificationMixedTransition X Z (f ≫ g) _ Λ _ hX hZ
          C.composite C.composite (𝟙 C.composite) hTop (compositeModels C.composite)).app K =
      ((moduleExceptionalSingleTorsionValueIso (f ≫ g) Λ C.composite hTop).hom.app K).hom := rfl
  have hm := moduleCartesianFirstTargetComparison f g Λ
    (hF := hRaw) (hC := firstModels C.first) (hG := secondModels C.targetCompactification)
    C F (compositeModels C.composite) hTop m sq a sqMid hj
  have hmK := congrArg (fun t => t.app K) hm
  have hc := congrArg (fun t => t.app K) (moduleCartesianCompositionMap_canonical f g Λ C)
  have hmK' := hmK.trans (congrArg
    (fun z => z ≫ (@moduleCompactificationMixedTransition X Z (f ≫ g) _ Λ _ hX hZ
      C.composite C.composite (𝟙 C.composite) hTop (compositeModels C.composite)).app K) hc)
  exact chosenImageSquareEquation _ _ _ _ _ _ _ _ _ hk hs ht hmK'

end AlgebraicGeometry.Scheme.EtaleCohomology
