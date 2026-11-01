/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionLeftUnitFace

/-! # Original left-unit face at the actual total open embeddings -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wA wB wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
  (C : Hom.DenseCompactification f)

omit [QuasiCompact f] in
/-- The mixed-model identity refinement uses the literal identity Cartesian square. -/
theorem leftUnitTowerTotalSquare : IsPullback C.j (𝟙 X) (𝟙 C.Xbar) C.j :=
  IsPullback.of_vert_isIso ⟨by simp⟩

variable (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hA : HasDerivedCategory.{wA}
    (ModuleSheaf (Hom.CompactifiedComposition.leftUnit C).first.Xbar Λ))
  (hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ))

/-- The original target open expansion, including its actual equality transport. -/
def moduleLeftUnitTargetExpansion :
    @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD ≅
      @moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX ⋙
        @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD :=
  eqToIso (@moduleDerivedLowerShriek_congr Λ _ C.Xbar X C.j ((𝟙 X) ≫ C.j)
    _ _ hD hX (Category.id_comp C.j).symm) ≪≫
    @moduleDerivedLowerShriekCompIso Λ _ C.Xbar X X C.j (𝟙 X) _ _ hD hX hX

/-- The original source open expansion of the actual supplied tower. -/
def moduleLeftUnitSourceExpansion :
    @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hB ≅
      @moduleDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX hA ⋙
      @moduleDerivedLowerShriek (Hom.CompactifiedComposition.leftUnit C).first.Xbar C.Xbar
        (leftUnitMiddleOpen C) _ Λ _ hA hB :=
  eqToIso (@moduleDerivedLowerShriek_congr Λ _ C.Xbar X C.j
    ((Hom.CompactifiedComposition.leftUnit C).first.j ≫ leftUnitMiddleOpen C)
    _ _ hB hX
      (Hom.CompactifiedComposition.leftUnit C).first_j_middleOpen.symm) ≪≫
    @moduleDerivedLowerShriekCompIso Λ _ C.Xbar
      (Hom.CompactifiedComposition.leftUnit C).first.Xbar X
      (leftUnitMiddleOpen C) (Hom.CompactifiedComposition.leftUnit C).first.j _ _ hB hA hX

/-- Actual total opens identify the original horizontal equation
with the mixed identity transition. -/
theorem moduleLeftUnitTowerTotalOpenEquation :
    UnitMateHorizontalEquation
      (@moduleDerivedProperRefinementComparison X
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar X
        (Hom.CompactifiedComposition.leftUnit C).first.j (𝟙 X) _ _
        (Hom.CompactifiedComposition.leftUnit C).first.p (leftUnitTowerSourceSquare C)
        Λ _ hX hA hX)
      (@moduleDerivedProperRefinementComparison X C.Xbar C.Xbar C.j C.j _ _
        (𝟙 C.Xbar) (leftUnitTowerTotalSquare C) Λ _ hX hB hD)
      (@moduleProperOpenMate Λ _ X
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar C.Xbar C.Xbar
        C.j (leftUnitMiddleOpen C)
        (Hom.CompactifiedComposition.leftUnit C).first.p (𝟙 C.Xbar) _ _
        (Hom.CompactifiedComposition.leftUnit C).isPullback_middleOpen.flip hX hA hD hB)
      (moduleLeftUnitTargetExpansion C Λ hX hD)
      (moduleLeftUnitSourceExpansion C Λ hX hA hB) :=
  @moduleDerivedProperRefinementComparison_hComp_transport Λ _ X
    (Hom.CompactifiedComposition.leftUnit C).first.Xbar X C.Xbar C.Xbar
    (Hom.CompactifiedComposition.leftUnit C).first.j (𝟙 X)
    (leftUnitMiddleOpen C) C.j _ _ _ _
    (Hom.CompactifiedComposition.leftUnit C).first.p (𝟙 C.Xbar)
    (leftUnitTowerSourceSquare C) (Hom.CompactifiedComposition.leftUnit C).isPullback_middleOpen
    hX hA hX hB hD C.j C.j _ _
    (Hom.CompactifiedComposition.leftUnit C).first_j_middleOpen (Category.id_comp C.j)
    (leftUnitTowerTotalSquare C)

end AlgebraicGeometry.Scheme.EtaleCohomology
