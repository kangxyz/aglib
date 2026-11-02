/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionLeftUnitFace

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
theorem unboundedLeftUnitTowerTotalSquare : IsPullback C.j (𝟙 X) (𝟙 C.Xbar) C.j :=
  IsPullback.of_vert_isIso ⟨by simp⟩

variable (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hA : HasDerivedCategory.{wA}
    (ModuleSheaf (Hom.CompactifiedComposition.leftUnit C).first.Xbar Λ))
  (hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ))

/-- The original target open expansion, including its actual equality transport. -/
def moduleUnboundedLeftUnitTargetExpansion :
    @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD ≅
      @moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX ⋙
        @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD :=
  eqToIso (@moduleUnboundedDerivedLowerShriek_congr X C.Xbar Λ _ hX hD
    C.j ((𝟙 X) ≫ C.j) _ _ (Category.id_comp C.j).symm) ≪≫
    @moduleUnboundedDerivedLowerShriekCompIso Λ _ C.Xbar X X C.j (𝟙 X) _ _ hD hX hX

/-- The original source open expansion of the actual supplied tower. -/
def moduleUnboundedLeftUnitSourceExpansion :
    @moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hB ≅
      @moduleUnboundedDerivedLowerShriek X (Hom.CompactifiedComposition.leftUnit C).first.Xbar
        (Hom.CompactifiedComposition.leftUnit C).first.j _ Λ _ hX hA ⋙
      @moduleUnboundedDerivedLowerShriek (Hom.CompactifiedComposition.leftUnit C).first.Xbar C.Xbar
        (unboundedLeftUnitMiddleOpen C) _ Λ _ hA hB :=
  eqToIso (@moduleUnboundedDerivedLowerShriek_congr X C.Xbar Λ _ hX hB C.j
    ((Hom.CompactifiedComposition.leftUnit C).first.j ≫ unboundedLeftUnitMiddleOpen C) _ _
      (Hom.CompactifiedComposition.leftUnit C).first_j_middleOpen.symm) ≪≫
    @moduleUnboundedDerivedLowerShriekCompIso Λ _ C.Xbar
      (Hom.CompactifiedComposition.leftUnit C).first.Xbar X
      (unboundedLeftUnitMiddleOpen C) (Hom.CompactifiedComposition.leftUnit C).first.j _ _ hB hA hX

/-- Actual total opens identify the original horizontal equation
with the mixed identity transition. -/
theorem moduleUnboundedLeftUnitTowerTotalOpenEquation :
    UnitMateHorizontalEquation
      (@moduleUnboundedDerivedProperRefinementComparison X
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar X
        (Hom.CompactifiedComposition.leftUnit C).first.j (𝟙 X) _ _
        (Hom.CompactifiedComposition.leftUnit C).first.p (unboundedLeftUnitTowerSourceSquare C)
        Λ _ hX hA hX)
      (@moduleUnboundedDerivedProperRefinementComparison X C.Xbar C.Xbar C.j C.j _ _
        (𝟙 C.Xbar) (unboundedLeftUnitTowerTotalSquare C) Λ _ hX hB hD)
      (@moduleUnboundedProperOpenMate
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar X C.Xbar C.Xbar
        (Hom.CompactifiedComposition.leftUnit C).first.p (unboundedLeftUnitMiddleOpen C)
        C.j (𝟙 C.Xbar) _ _
        (Hom.CompactifiedComposition.leftUnit C).isPullback_middleOpen.flip
        Λ _ hA hX hB hD)
      (moduleUnboundedLeftUnitTargetExpansion C Λ hX hD)
      (moduleUnboundedLeftUnitSourceExpansion C Λ hX hA hB) :=
  @moduleUnboundedDerivedProperRefinementComparison_hComp_transport Λ _ X
    (Hom.CompactifiedComposition.leftUnit C).first.Xbar X C.Xbar C.Xbar
    (Hom.CompactifiedComposition.leftUnit C).first.j (𝟙 X)
    (unboundedLeftUnitMiddleOpen C) C.j _ _ _ _
    (Hom.CompactifiedComposition.leftUnit C).first.p (𝟙 C.Xbar)
    (unboundedLeftUnitTowerSourceSquare C)
    (Hom.CompactifiedComposition.leftUnit C).isPullback_middleOpen
    hX hA hX hB hD C.j C.j _ _
    (Hom.CompactifiedComposition.leftUnit C).first_j_middleOpen (Category.id_comp C.j)
    (unboundedLeftUnitTowerTotalSquare C)

end AlgebraicGeometry.Scheme.EtaleCohomology
