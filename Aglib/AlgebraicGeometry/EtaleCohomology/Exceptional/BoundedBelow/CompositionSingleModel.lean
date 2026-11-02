/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelTorsion

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
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]

variable (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  (hRaw : HasDerivedCategory.{wRaw} (ModuleSheaf F.Xbar Λ))
  (hTop : HasDerivedCategory.{wTop} (ModuleSheaf C.composite.Xbar Λ))

/-- The original chosen compositor transported by original single-value comparisons.
Its equality to the actual Cartesian map is a separate proved normalization. -/
def moduleExceptionalCompositionSingleModelIso :
    moduleCompactificationSingleTorsionValue Λ F hRaw ⋙
        moduleCompactificationSingleTorsionValue Λ C.targetCompactification
          (secondModels C.targetCompactification) ≅
      moduleCompactificationSingleTorsionValue Λ C.composite hTop :=
  (compositionPairIso
    (moduleExceptionalSingleTorsionValueIso f Λ F hRaw)
    (moduleExceptionalSingleTorsionValueIso g Λ C.targetCompactification
      (secondModels C.targetCompactification))).symm ≪≫
    moduleExceptionalCompositionIso f g Λ ≪≫
    moduleExceptionalSingleTorsionValueIso (f ≫ g) Λ C.composite hTop

/-- The native comparison square retains the original chosen compositor and comparisons. -/
theorem moduleExceptionalCompositionSingleModelIso_comparison :
    compositionPairIso
        (moduleExceptionalSingleTorsionValueIso f Λ F hRaw)
        (moduleExceptionalSingleTorsionValueIso g Λ C.targetCompactification
          (secondModels C.targetCompactification)) ≪≫
      moduleExceptionalCompositionSingleModelIso f g Λ C F hRaw hTop =
    moduleExceptionalCompositionIso f g Λ ≪≫
      moduleExceptionalSingleTorsionValueIso (f ≫ g) Λ C.composite hTop := by
  simp only [moduleExceptionalCompositionSingleModelIso, Iso.self_symm_id_assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology
