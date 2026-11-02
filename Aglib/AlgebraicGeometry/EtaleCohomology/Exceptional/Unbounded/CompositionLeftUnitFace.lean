/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionRefinementHorizontal
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionUnitRefinements

/-! # The original mixed-model open face of the left unit tower

This is the actual horizontal original-unit equation. The two models on the
same compactifying scheme remain explicit and independent. Contraction of the
identity factorization and the final proper-image stage are separate steps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wA wB wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
  (C : Hom.DenseCompactification f)

/-- The original first refinement of the unit tower supplies its Cartesian source square. -/
theorem unboundedLeftUnitTowerSourceSquare :
    IsPullback (Hom.CompactifiedComposition.leftUnit C).first.j (𝟙 X)
      (Hom.CompactifiedComposition.leftUnit C).first.p (𝟙 X) :=
  Hom.DenseCompactification.isPullback_open
    (Hom.CompactifiedComposition.leftUnitFirstRefinement C)

/-- The original middle open, with its literal ambient endpoint displayed. -/
abbrev unboundedLeftUnitMiddleOpen :
    (Hom.CompactifiedComposition.leftUnit C).first.Xbar ⟶ C.Xbar :=
  (Hom.CompactifiedComposition.leftUnit C).middleOpen

instance unboundedLeftUnitMiddleOpen_isOpenImmersion :
    IsOpenImmersion (unboundedLeftUnitMiddleOpen C) :=
  inferInstanceAs (IsOpenImmersion (Hom.CompactifiedComposition.leftUnit C).middleOpen)

variable (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hA : HasDerivedCategory.{wA}
    (ModuleSheaf (Hom.CompactifiedComposition.leftUnit C).first.Xbar Λ))
  (hB : HasDerivedCategory.{wB} (ModuleSheaf C.Xbar Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ))

/-- Original mixed-model refinement units and the actual central mate satisfy the unit face. -/
theorem moduleUnboundedLeftUnitTowerOpenEquation :
    UnitMateHorizontalEquation
      (@moduleUnboundedDerivedProperRefinementComparison X
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar X
        (Hom.CompactifiedComposition.leftUnit C).first.j (𝟙 X) _ _
        (Hom.CompactifiedComposition.leftUnit C).first.p (unboundedLeftUnitTowerSourceSquare C)
        Λ _ hX hA hX)
      (@moduleUnboundedDerivedProperRefinementComparison X C.Xbar C.Xbar
        ((Hom.CompactifiedComposition.leftUnit C).first.j ≫
          (unboundedLeftUnitMiddleOpen C))
        ((𝟙 X) ≫ C.j) _ _ (𝟙 C.Xbar)
        ((unboundedLeftUnitTowerSourceSquare C).paste_horiz
          (Hom.CompactifiedComposition.leftUnit C).isPullback_middleOpen)
        Λ _ hX hB hD)
      (@moduleUnboundedProperOpenMate
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar X C.Xbar C.Xbar
        (Hom.CompactifiedComposition.leftUnit C).first.p (unboundedLeftUnitMiddleOpen C)
        C.j (𝟙 C.Xbar) _ _
        (Hom.CompactifiedComposition.leftUnit C).isPullback_middleOpen.flip
        Λ _ hA hX hB hD)
      (@moduleUnboundedDerivedLowerShriekCompIso Λ _ C.Xbar X X C.j (𝟙 X) _ _ hD hX hX)
      (@moduleUnboundedDerivedLowerShriekCompIso Λ _ C.Xbar
        (Hom.CompactifiedComposition.leftUnit C).first.Xbar X
        (unboundedLeftUnitMiddleOpen C)
        (Hom.CompactifiedComposition.leftUnit C).first.j _ _ hB hA hX) :=
  @moduleUnboundedDerivedProperRefinementComparison_hComp Λ _ X
    (Hom.CompactifiedComposition.leftUnit C).first.Xbar X C.Xbar C.Xbar
    (Hom.CompactifiedComposition.leftUnit C).first.j (𝟙 X)
    (unboundedLeftUnitMiddleOpen C) C.j _ _ _ _
    (Hom.CompactifiedComposition.leftUnit C).first.p (𝟙 C.Xbar)
    (unboundedLeftUnitTowerSourceSquare C)
    (Hom.CompactifiedComposition.leftUnit C).isPullback_middleOpen
    hX hA hX hB hD

end AlgebraicGeometry.Scheme.EtaleCohomology
