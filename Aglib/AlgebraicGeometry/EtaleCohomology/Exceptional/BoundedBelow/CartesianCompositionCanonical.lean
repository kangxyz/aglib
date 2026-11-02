/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianCompositionMap

/-! # The Cartesian presentation retains the original canonical supplied-tower map -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wF wG wFG
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g] (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ F : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf F.Xbar Λ)]
  [targetModels : ∀ G : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf G.Xbar Λ)]
  [compositeModels : ∀ H : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf H.Xbar Λ)]
  (C : Hom.CompactifiedComposition f g)

omit [QuasiCompact f] in
/-- At the original pullback presentation this is the unchanged supplied composition map. -/
theorem moduleCartesianCompositionMap_canonical :
    moduleCartesianCompositionMap C C.first C.middleOpen C.isPullback_middleOpen
        C.first_j_middleOpen Λ hX hY hZ
        (firstModels C.first) (targetModels C.targetCompactification)
        (compositeModels C.composite) =
      (moduleCompactifiedCompositionAmbientIso f g Λ C).hom := by
  apply NatTrans.ext
  funext K
  exact (moduleCompactifiedCompositionAmbientIso_formula f g Λ (C := C) K).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
