/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionComparison

/-! # Actual dense refinement between the triple-composition intermediate models -/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition

variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact h] (T : TripleCompactifiedComposition f g h)

/-- The pullback-pasting map preserves the actual original source embedding. -/
@[reassoc (attr := simp)]
lemma leftIntermediateIso_source :
    T.leftInner.composite.j ≫ T.leftIntermediateIso.hom = T.leftOuter.first.j := by
  let m : T.leftOuter.first.Xbar ⟶ T.first.Xbar := T.leftOuter.middleOpen
  have hm : T.leftIntermediateIso.hom ≫ m = T.innerToFirst :=
    T.leftIntermediateIso_hom_middleOpen
  have hs : T.leftOuter.first.j ≫ m = T.first.j :=
    T.leftOuter.first_j_middleOpen
  let : Mono m := inferInstanceAs (Mono T.leftOuter.middleOpen)
  apply (cancel_mono m).1
  rw [Category.assoc, hm, hs]
  exact T.leftInner_j_innerToFirst


/-- The actual ambient isomorphism gives a genuine dense-compactification refinement. -/
def leftIntermediateRefinement : T.leftInner.composite ⟶ T.leftOuter.first where
  hom := T.leftIntermediateIso.hom
  isProper_hom := inferInstance
  open_fac := T.leftIntermediateIso_source
  base_fac := T.leftIntermediateIso_hom_p

end AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition
