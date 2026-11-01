/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageTargetRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionMixedRefinementWhole
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianCompositionMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianCompositionIdentity

/-! # Change only the supplied total model using the original mixed identity refinement -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wF wG wT₀ wT₁
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g] (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  (C : Hom.CompactifiedComposition f g)
  [hF : HasDerivedCategory.{wF} (ModuleSheaf C.first.Xbar Λ)]
  [hG : HasDerivedCategory.{wG} (ModuleSheaf C.targetCompactification.Xbar Λ)]
  (hT₀ : HasDerivedCategory.{wT₀} (ModuleSheaf C.sourceCompactification.Xbar Λ))
  (hT₁ : HasDerivedCategory.{wT₁} (ModuleSheaf C.sourceCompactification.Xbar Λ))

/-- Only the original total-model map changes; no global family is patched. -/
theorem moduleCartesianCompositionMap_singleTarget :
    ImageTargetRefinementEquation
      (K := (@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
        @moduleDerivedLowerShriek X C.first.Xbar C.first.j _ Λ _ hX hF)
      (Q := @moduleDerivedDirectImage Y Λ _ C.first.Xbar C.first.p hY hF)
      (I := @moduleDerivedLowerShriek Y C.targetCompactification.Xbar
        C.targetCompactification.j _ Λ _ hY hG)
      (P := @moduleDerivedDirectImage Z Λ _ C.targetCompactification.Xbar
        C.targetCompactification.p hZ hG)
      (J₀ := (@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
        @moduleDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hT₀)
      (J₁ := (@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
        @moduleDerivedLowerShriek X C.sourceCompactification.Xbar
          C.sourceCompactification.j _ Λ _ hX hT₁)
      (S₀ := @moduleDerivedDirectImage Z Λ _ C.sourceCompactification.Xbar C.composite.p hZ hT₀)
      (S₁ := @moduleDerivedDirectImage Z Λ _ C.sourceCompactification.Xbar C.composite.p hZ hT₁)
      (@moduleCompactificationMixedTransition X Z (f ≫ g) _ Λ _ hX hZ
        C.composite C.composite (𝟙 C.composite) hT₁ hT₀)
      (moduleCartesianCompositionMap C C.first C.middleOpen C.isPullback_middleOpen
        C.first_j_middleOpen Λ hX hY hZ hF hG hT₀)
      (moduleCartesianCompositionMap C C.first C.middleOpen C.isPullback_middleOpen
        C.first_j_middleOpen Λ hX hY hZ hF hG hT₁) := by
  let a : C.Refinement C := ⟨𝟙 _, 𝟙 _, by
    change (𝟙 C.sourceCompactification.Xbar) ≫ C.sourceCompactification.p =
      C.sourceCompactification.p ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]⟩
  have ha : a.intermediate = 𝟙 C.first := Subsingleton.elim _ _
  have ht : a.target = 𝟙 C.targetCompactification := rfl
  have hs : a.source = 𝟙 C.composite := rfl
  have hw := @moduleCompactifiedCompositionMixedRefinement_whole X Y Z f g _ _ Λ _
    hX hY hZ C C a hF hF hG hG hT₁ hT₀
    (moduleCartesianCompositionMap C C.first C.middleOpen C.isPullback_middleOpen
      C.first_j_middleOpen Λ hX hY hZ hF hG hT₀)
    (moduleCartesianCompositionMap C C.first C.middleOpen C.isPullback_middleOpen
      C.first_j_middleOpen Λ hX hY hZ hF hG hT₁)
    (imageCompositionMap_formula _ _ _) (imageCompositionMap_formula _ _ _)
  rw [ha, ht, hs] at hw
  exact imageTargetRefinementEquation _ _ _ _ _
    (moduleDerivedCompactificationImageIdentity_torsion Λ
      (hX := hX) (hS := hY) (hC := hF) C.first)
    (moduleDerivedCompactificationImageIdentity Λ
      (hX := hY) (hS := hZ) (hC := hG) C.targetCompactification) hw

end AlgebraicGeometry.Scheme.EtaleCohomology
