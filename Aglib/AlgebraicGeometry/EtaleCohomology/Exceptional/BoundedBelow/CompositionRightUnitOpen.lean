/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitOpenFace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.Coherence
public import Aglib.CategoryTheory.Functor.ImageRightUnitIdentity
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekCompositionCoherence

/-! # Normalization of the original right-unit source-open refinement -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wA wB
variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
  (C : Hom.DenseCompactification f)

/-- The literal first ambient of the supplied right-unit tower. -/
abbrev rightUnitFirstAmbient := (Hom.CompactifiedComposition.rightUnit C).first.Xbar

/-- The literal first open of the supplied right-unit tower. -/
abbrev rightUnitFirstOpen := (Hom.CompactifiedComposition.rightUnit C).first.j

variable (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hA : HasDerivedCategory.{wA} (ModuleSheaf (rightUnitFirstAmbient C) Λ)]
  [hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ)]

/-- The original expansion of the final open through the literal first model. -/
def moduleRightUnitOpenExpansion :
    moduleDerivedLowerShriek C.j Λ ≅
      moduleDerivedLowerShriek (rightUnitFirstOpen C) Λ ⋙
        moduleDerivedLowerShriek (rightUnitMiddleOpen C) Λ := by
  let e : C.j = rightUnitFirstOpen C ≫ rightUnitMiddleOpen C :=
    (Hom.CompactifiedComposition.rightUnit C).first_j_middleOpen.symm
  have he : Etale (rightUnitFirstOpen C ≫ rightUnitMiddleOpen C) :=
    e ▸ (inferInstance : Etale C.j)
  exact eqToIso (@moduleDerivedLowerShriek_congr Λ _ C.Xbar X C.j
      (rightUnitFirstOpen C ≫ rightUnitMiddleOpen C) inferInstance he hB hX e) ≪≫
    @moduleDerivedLowerShriekCompIso Λ _ C.Xbar (rightUnitFirstAmbient C) X
      (rightUnitMiddleOpen C) (rightUnitFirstOpen C) _ _ hB hA hX

/-- The same-first-model source identity expansion; this does not involve `hB`. -/
def moduleRightUnitFirstIdentityExpansion :
    moduleDerivedLowerShriek (rightUnitFirstOpen C) Λ ≅
      moduleDerivedLowerShriek (rightUnitFirstOpen C) Λ ⋙
        moduleDerivedLowerShriek (𝟙 (rightUnitFirstAmbient C)) Λ :=
  eqToIso (moduleDerivedLowerShriek_congr Λ (Category.comp_id (rightUnitFirstOpen C)).symm) ≪≫
    moduleDerivedLowerShriekCompIso Λ (𝟙 (rightUnitFirstAmbient C)) (rightUnitFirstOpen C)

/-- The original refinement of the middle open by its own source identity. -/
abbrev moduleRightUnitMiddleOpenDelta :=
  moduleDerivedProperRefinementComparison (𝟙 (rightUnitFirstAmbient C)) (rightUnitMiddleOpen C)
    (rightUnitMiddleOpen C) (rightUnitOpenMiddleSquare C) Λ

/-- The original middle-open refinement with only its first-model identity contracted. -/
def moduleRightUnitMiddleOpenToDirect :
    moduleDerivedLowerShriek (rightUnitMiddleOpen C) Λ ⟶
      moduleDerivedDirectImage Λ (rightUnitMiddleOpen C) :=
  moduleRightUnitMiddleOpenDelta C Λ ≫
    Functor.whiskerRight (moduleDerivedLowerShriekIdIso Λ (rightUnitFirstAmbient C)).hom
      (moduleDerivedDirectImage Λ (rightUnitMiddleOpen C)) ≫
    (Functor.leftUnitor (moduleDerivedDirectImage Λ (rightUnitMiddleOpen C))).hom

omit [QuasiCompact f] hB in
/-- The identity expansion has its actual original lower-shriek identity component. -/
theorem moduleRightUnitFirstIdentityExpansion_hom_app
    (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleRightUnitFirstIdentityExpansion C Λ).hom.app K =
      (moduleDerivedLowerShriekIdIso Λ (rightUnitFirstAmbient C)).inv.app
        ((moduleDerivedLowerShriek (rightUnitFirstOpen C) Λ).obj K) :=
  rightIdentityExpansion_app
    (eqToIso (moduleDerivedLowerShriek_congr Λ (Category.comp_id (rightUnitFirstOpen C))))
    (moduleDerivedLowerShriekCompIso Λ (𝟙 (rightUnitFirstAmbient C)) (rightUnitFirstOpen C))
    (moduleDerivedLowerShriekIdIso Λ (rightUnitFirstAmbient C))
    (moduleDerivedLowerShriekCompIso_id_comp Λ (rightUnitFirstOpen C)) K

/-- The actual first-refinement open face is normalized without identifying final models. -/
theorem moduleRightUnitOpenEquation :
    RightUnitOpenEquation (moduleRightUnitOpenExpansion C Λ).symm
      (moduleDerivedRefinementComparison
        (Hom.CompactifiedComposition.rightUnitFirstRefinement C) Λ)
      (moduleRightUnitMiddleOpenToDirect C Λ) := by
  apply rightUnitOpenEquation_of_horizontal
    (moduleDerivedRefinementComparison (𝟙 (Hom.CompactifiedComposition.rightUnit C).first) Λ)
    _ _ (moduleRightUnitOpenExpansion C Λ) (moduleRightUnitFirstIdentityExpansion C Λ)
    (moduleDerivedDirectImageIdIso Λ (rightUnitFirstAmbient C))
    (moduleDerivedLowerShriekIdIso Λ (rightUnitFirstAmbient C))
    (moduleRightUnitMiddleOpenDelta C Λ)
  · exact moduleRightUnitOpenHorizontalEquation C Λ hX hA hB
  · exact identityRefinement_inv_app _ _
      (moduleDerivedRefinementComparison_id Λ (Hom.CompactifiedComposition.rightUnit C).first)
  · intro K
    exact (moduleDerivedProperRefinementComparison_identitySourceMate
      (𝟙 (rightUnitFirstAmbient C)) (rightUnitMiddleOpen C) (rightUnitMiddleOpen C)
      (rightUnitOpenMiddleSquare C) Λ K).symm
  · exact moduleRightUnitFirstIdentityExpansion_hom_app C Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
