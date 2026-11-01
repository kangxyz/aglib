/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.TorsionCoherence

/-! # Original components of the supplied-tower composition isomorphism

The canonical torsion comparison is identified with the already specified
global mixed mate. This is a formula for the accepted map, not a replacement
construction on isomorphic objects.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wZ wF wG wFG

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g] (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]
  (C : Hom.CompactifiedComposition f g)

/-- The local derived-category model on `ModuleSheaf C.first.Xbar Λ`. -/
local instance : HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ) := firstModels C.first
/-- The local derived-category model on `ModuleSheaf C.targetCompactification.Xbar Λ`. -/
local instance : HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ) :=
  secondModels C.targetCompactification
/-- The local derived-category model on `ModuleSheaf C.sourceCompactification.Xbar Λ`. -/
local instance : HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ) :=
  compositeModels C.composite

/-- The exact open compositor used in the accepted supplied-tower construction. -/
def moduleCompactifiedCompositionOpenIso :
    moduleDerivedLowerShriek C.first.j Λ ⋙ moduleDerivedLowerShriek C.middleOpen Λ ≅
      moduleDerivedLowerShriek C.sourceCompactification.j Λ :=
  (moduleDerivedLowerShriekCompIso Λ C.middleOpen C.first.j).symm ≪≫
    eqToIso (moduleDerivedLowerShriek_congr Λ C.first_j_middleOpen)

omit [QuasiCompact f] in
/-- The accepted ambient comparison retains the original global proper/open
mate, the original open compositor and the original proper compositor. -/
theorem moduleCompactifiedCompositionAmbientIso_hom_app
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    (moduleCompactifiedCompositionAmbientIso f g Λ C).hom.app K =
      (moduleDerivedDirectImage Λ C.targetCompactification.p).map
        ((moduleProperOpenMate Λ C.targetCompactification.j C.middleOpen
          C.first.p C.sourceCompactification.p C.isPullback_middleOpen.flip).app
            ((moduleDerivedLowerShriek C.first.j Λ).obj K.obj)) ≫
      (moduleDerivedDirectImage Λ C.targetCompactification.p).map
        ((moduleDerivedDirectImage Λ C.sourceCompactification.p).map
          ((moduleCompactifiedCompositionOpenIso f g Λ C).hom.app K.obj)) ≫
      (moduleDerivedDirectImageCompIso Λ C.targetCompactification.p
        C.sourceCompactification.p).inv.app
          ((moduleDerivedLowerShriek C.sourceCompactification.j Λ).obj K.obj) := by
  change (moduleDerivedDirectImage Λ C.targetCompactification.p).map
      ((moduleProperOpenComparison Λ C.sourceCompactification.p C.first.p
        C.targetCompactification.j C.middleOpen C.isPullback_middleOpen).app
          ⟨(moduleDerivedLowerShriek C.first.j Λ).obj K.obj,
            moduleDerivedLowerShriek_preservesTorsionCohomology C.first.j Λ K.property⟩) ≫
      _ ≫ _ = _
  rw [moduleProperOpenComparison_eq_mate_app]
  rfl

/-- Inverse canonical comparison along a refinement is exactly the original
contravariant transition after forgetting the target torsion property. -/
theorem moduleCompactificationTorsionComparison_inv_refinement
    {E F : Hom.DenseCompactification f} (a : E ⟶ F)
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleCompactificationTorsionComparison f Λ E F).inv.app K).hom =
      (moduleCompactificationTransition Λ a).app K := by
  change (moduleCompactificationComparison f Λ E F).inv.app K = _
  rw [moduleCompactificationComparison_refinement f Λ a]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
