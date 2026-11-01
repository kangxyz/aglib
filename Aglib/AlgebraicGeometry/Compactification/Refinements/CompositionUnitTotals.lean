/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionUnits
public import Aglib.AlgebraicGeometry.Compactification.Refinements.ArrowEquality

/-! # Actual total refinements of the composition unit towers -/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.Hom.CompactifiedComposition
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (C : DenseCompactification f)

/-- The total left-unit compactification has its original identity ambient refinement. -/
def leftUnitTotalRefinement :
    DenseCompactification.ofArrowEq (Category.id_comp f) (leftUnit C).composite ⟶ C where
  hom := 𝟙 C.Xbar
  isProper_hom := inferInstanceAs (IsProper (𝟙 C.Xbar))
  open_fac := Category.comp_id C.j
  base_fac := rfl

/-- The total right-unit compactification has its original identity ambient refinement. -/
def rightUnitTotalRefinement :
    DenseCompactification.ofArrowEq (Category.comp_id f) (rightUnit C).composite ⟶ C where
  hom := 𝟙 C.Xbar
  isProper_hom := inferInstanceAs (IsProper (𝟙 C.Xbar))
  open_fac := Category.comp_id C.j
  base_fac := by
    change (𝟙 C.Xbar) ≫ C.p = C.p ≫ 𝟙 Y
    simp only [Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Scheme.Hom.CompactifiedComposition
