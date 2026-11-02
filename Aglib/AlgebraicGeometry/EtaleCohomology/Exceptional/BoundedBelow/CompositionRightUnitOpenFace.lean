/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRightUnitFace
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementHorizontal
public import Aglib.CategoryTheory.Functor.ImageRightUnitOpen

/-! # The original horizontal source-open face of the right-unit refinement

Only identities on the first ambient model occur in this face. The model on
the supplied final compactification remains independent.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wA wB
variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
  (C : Hom.DenseCompactification f)

/-- The source square is the actual identity refinement of the first model. -/
theorem rightUnitOpenSourceSquare :
    IsPullback (Hom.CompactifiedComposition.rightUnit C).first.j (𝟙 X)
      (𝟙 (Hom.CompactifiedComposition.rightUnit C).first.Xbar)
      (Hom.CompactifiedComposition.rightUnit C).first.j :=
  Hom.DenseCompactification.isPullback_open (𝟙 (Hom.CompactifiedComposition.rightUnit C).first)

omit [QuasiCompact f] in
/-- The middle square is Cartesian because the original middle open is a monomorphism. -/
theorem rightUnitOpenMiddleSquare :
    IsPullback (𝟙 (Hom.CompactifiedComposition.rightUnit C).first.Xbar)
      (𝟙 (Hom.CompactifiedComposition.rightUnit C).first.Xbar)
      (rightUnitMiddleOpen C) (rightUnitMiddleOpen C) :=
  IsPullback.of_vert_isIso_mono ⟨by simp⟩

/-- The total square is the original first-model refinement of the unit tower. -/
theorem rightUnitOpenTotalSquare :
    IsPullback (Hom.CompactifiedComposition.rightUnit C).first.j (𝟙 X)
      (rightUnitMiddleOpen C) C.j :=
  Hom.DenseCompactification.isPullback_open
    (Hom.CompactifiedComposition.rightUnitFirstRefinement C)

variable (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hA : HasDerivedCategory.{wA}
    (ModuleSheaf (Hom.CompactifiedComposition.rightUnit C).first.Xbar Λ))
  (hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ))

/-- The original right-unit source refinement has its exact horizontal open face. -/
theorem moduleRightUnitOpenHorizontalEquation :
    UnitMateHorizontalEquation
      (@moduleDerivedProperRefinementComparison X
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar
        (Hom.CompactifiedComposition.rightUnit C).first.j
        (Hom.CompactifiedComposition.rightUnit C).first.j _ _
        (𝟙 _) (rightUnitOpenSourceSquare C) Λ _ hX hA hA)
      (@moduleDerivedProperRefinementComparison X
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar C.Xbar
        (Hom.CompactifiedComposition.rightUnit C).first.j C.j _ _
        (rightUnitMiddleOpen C) (rightUnitOpenTotalSquare C) Λ _ hX hA hB)
      (@moduleProperOpenMate Λ _
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar C.Xbar
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar
        (rightUnitMiddleOpen C) (𝟙 _) (𝟙 _) (rightUnitMiddleOpen C) _ _
        (rightUnitOpenMiddleSquare C).flip hA hA hB hA)
      (eqToIso (@moduleDerivedLowerShriek_congr Λ _ C.Xbar X C.j
        ((Hom.CompactifiedComposition.rightUnit C).first.j ≫ rightUnitMiddleOpen C)
        _ _ hB hX (Hom.CompactifiedComposition.rightUnit C).first_j_middleOpen.symm) ≪≫
        @moduleDerivedLowerShriekCompIso Λ _ C.Xbar
          (Hom.CompactifiedComposition.rightUnit C).first.Xbar X
          (rightUnitMiddleOpen C) (Hom.CompactifiedComposition.rightUnit C).first.j
          _ _ hB hA hX)
      (eqToIso (@moduleDerivedLowerShriek_congr Λ _
        (Hom.CompactifiedComposition.rightUnit C).first.Xbar X
        (Hom.CompactifiedComposition.rightUnit C).first.j
        ((Hom.CompactifiedComposition.rightUnit C).first.j ≫ 𝟙 _) _ _ hA hX
        (Category.comp_id _).symm) ≪≫
        @moduleDerivedLowerShriekCompIso Λ _
          (Hom.CompactifiedComposition.rightUnit C).first.Xbar
          (Hom.CompactifiedComposition.rightUnit C).first.Xbar X
          (𝟙 _) (Hom.CompactifiedComposition.rightUnit C).first.j _ _ hA hA hX) :=
  @moduleDerivedProperRefinementComparison_hComp_transport Λ _ X
    (Hom.CompactifiedComposition.rightUnit C).first.Xbar
    (Hom.CompactifiedComposition.rightUnit C).first.Xbar
    (Hom.CompactifiedComposition.rightUnit C).first.Xbar C.Xbar
    (Hom.CompactifiedComposition.rightUnit C).first.j
    (Hom.CompactifiedComposition.rightUnit C).first.j (𝟙 _) (rightUnitMiddleOpen C)
    _ _ _ _ (𝟙 _) (rightUnitMiddleOpen C)
    (rightUnitOpenSourceSquare C) (rightUnitOpenMiddleSquare C)
    hX hA hA hA hB
    (Hom.CompactifiedComposition.rightUnit C).first.j C.j _ _
    (Category.comp_id _) (Hom.CompactifiedComposition.rightUnit C).first_j_middleOpen
    (rightUnitOpenTotalSquare C)

end AlgebraicGeometry.Scheme.EtaleCohomology
