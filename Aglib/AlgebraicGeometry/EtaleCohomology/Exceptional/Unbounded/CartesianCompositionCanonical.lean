/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianUnderlyingMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModelMaps

/-! # The Cartesian presentation retains the original canonical supplied-tower map -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard
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
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The local derived-category model on `ModuleSheaf C.first.Xbar Λ`. -/
local instance unboundedCartesianCanonicalFirst :
    HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ) := firstModels C.first
/-- The local derived-category model on `ModuleSheaf C.targetCompactification.Xbar Λ`. -/
local instance unboundedCartesianCanonicalTarget :
    HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ) :=
  targetModels C.targetCompactification
/-- The local derived-category model on `ModuleSheaf C.sourceCompactification.Xbar Λ`. -/
local instance unboundedCartesianCanonicalTotal :
    HasDerivedCategory.{wFG} (ModuleSheaf C.sourceCompactification.Xbar Λ) :=
  compositeModels C.composite

/-- The category structure for the specified derived-category model. -/
local instance unboundedCartesianCanonicalCategory :
    Category.{wFG} (@DerivedCategory (ModuleSheaf C.sourceCompactification.Xbar Λ)
      inferInstance inferInstance (compositeModels C.composite)) :=
  @instCategoryDerivedCategory (ModuleSheaf C.sourceCompactification.Xbar Λ)
    inferInstance inferInstance (compositeModels C.composite)

omit [QuasiCompact f] in
/-- At the original pullback presentation this is the unchanged supplied composition map. -/
theorem moduleUnboundedCartesianCompositionUnderlyingMap_canonical :
    moduleUnboundedCartesianCompositionUnderlyingMap C C.first C.middleOpen C.isPullback_middleOpen
        C.first_j_middleOpen Λ hX hY hZ
        (firstModels C.first) (targetModels C.targetCompactification)
        (compositeModels C.composite) =
      (moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ).hom := by
  exact imageCompositionMap_eq _ _ _ _
    (moduleUnboundedCompactifiedCompositionIso_formula f g Λ
      (firstModels := firstModels) (secondModels := targetModels)
      (compositeModels := compositeModels) C N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
