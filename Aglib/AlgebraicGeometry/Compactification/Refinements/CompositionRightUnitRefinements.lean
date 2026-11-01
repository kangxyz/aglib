/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionUnitRefinements
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionUnitTotals

/-! # The original first-to-total refinement of the right-unit tower -/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.Hom.CompactifiedComposition
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (C : DenseCompactification f)

/-- The actual first model maps to the actual total ambient, retaining its composite proper map. -/
def rightUnitFirstToTotalRefinement :
    (rightUnit C).first ⟶
      DenseCompactification.ofArrowEq (Category.comp_id f) (rightUnit C).composite where
  hom := (rightUnit C).middleOpen
  isProper_hom := (rightUnitFirstRefinement C).isProper_hom
  open_fac := (rightUnit C).first_j_middleOpen
  base_fac := by
    change (rightUnit C).middleOpen ≫ (C.p ≫ 𝟙 Y) = (rightUnit C).first.p
    exact (congrArg (fun k : C.Xbar ⟶ Y => (rightUnit C).middleOpen ≫ k)
      (Category.comp_id C.p)).trans (rightUnitFirstRefinement C).base_fac

/-- The two actual refinements compose to the original first refinement. -/
theorem rightUnitFirstToTotalRefinement_comp :
    rightUnitFirstToTotalRefinement C ≫ rightUnitTotalRefinement C =
      rightUnitFirstRefinement C := by
  apply DenseCompactification.Refinement.ext
  exact Category.comp_id (rightUnit C).middleOpen

end AlgebraicGeometry.Scheme.Hom.CompactifiedComposition
