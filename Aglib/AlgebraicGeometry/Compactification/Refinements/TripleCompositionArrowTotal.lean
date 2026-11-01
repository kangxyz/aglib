/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionTotal
public import Aglib.AlgebraicGeometry.Compactification.Refinements.ArrowEquality

/-! # Compare literal source-identity transport with original arrow-equality transport -/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  (T : TripleCompactifiedComposition f g h)

/-- The right total compactification in the actual scheme-arrow equality family. -/
def rightTotalArrowTransport : DenseCompactification ((f ≫ g) ≫ h) :=
  DenseCompactification.ofArrowEq (Category.assoc f g h).symm T.rightOuter.composite

/-- Genuine identity-ambient refinement; the identity source composition is not discarded. -/
def rightTotalSourceToArrow : T.rightTotalTransport ⟶ T.rightTotalArrowTransport where
  hom := 𝟙 T.first.Xbar
  isProper_hom := inferInstanceAs (IsProper (𝟙 T.first.Xbar))
  open_fac := by
    change ((𝟙 X) ≫ T.first.j) ≫ 𝟙 T.first.Xbar = T.first.j
    simp only [Category.id_comp, Category.comp_id]
  base_fac := Category.id_comp _

/-- The total comparison into the arrow-equality target factors through the accepted total map. -/
def totalArrowRefinement : T.leftOuter.composite ⟶ T.rightTotalArrowTransport :=
  T.totalRefinement ≫ T.rightTotalSourceToArrow

@[simp]
theorem totalArrowRefinement_hom : T.totalArrowRefinement.hom = 𝟙 T.first.Xbar :=
  Category.id_comp _

/-- This is a literal factorization of the existing total refinement, not a replacement map. -/
theorem totalArrowRefinement_factorization :
    T.totalRefinement ≫ T.rightTotalSourceToArrow = T.totalArrowRefinement := rfl

end AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition
