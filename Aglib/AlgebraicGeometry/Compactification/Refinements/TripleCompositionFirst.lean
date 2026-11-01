/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionRefinement

/-! # The first compactification in the two triple-composition routes -/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition

variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact g] [QuasiCompact h] (T : TripleCompactifiedComposition f g h)

/-- The original iterated open restriction is Cartesian over the uncut first ambient. -/
theorem isPullback_first :
    IsPullback (T.leftInner.middleOpen ≫ T.innerToFirst) T.leftInner.first.p
      T.first.p T.middle.j := by
  have hp : IsPullback (T.leftInner.middleOpen ≫ T.innerToFirst) T.leftInner.first.p
      T.first.p (T.tail.first.j ≫ T.tail.middleOpen) :=
    T.leftInner.isPullback_middleOpen.paste_horiz
      (DenseCompactification.isPullback_openRestriction
        (f ≫ T.tail.first.j) T.tail.middleOpen T.firstOverMiddleOpen)
  have hj : T.tail.first.j ≫ T.tail.middleOpen = T.middle.j :=
    T.tail.first_j_middleOpen
  exact (congrArg
    (fun k : Y ⟶ T.middle.Xbar =>
      IsPullback (T.leftInner.middleOpen ≫ T.innerToFirst) T.leftInner.first.p T.first.p k)
    hj).mp hp


/-- The two first-map models are related by the original pasted pullback cone. -/
def firstIso : T.leftInner.first.Xbar ≅ T.rightOuter.first.Xbar :=
  T.isPullback_first.flip.isoPullback

@[reassoc (attr := simp)]
lemma firstIso_hom_p : T.firstIso.hom ≫ T.rightOuter.first.p = T.leftInner.first.p :=
  T.isPullback_first.flip.isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma firstIso_hom_middleOpen :
    T.firstIso.hom ≫ T.rightOuter.middleOpen = T.leftInner.middleOpen ≫ T.innerToFirst :=
  T.isPullback_first.flip.isoPullback_hom_snd

/-- The comparison fixes the original source, not merely its isomorphism class. -/
@[reassoc (attr := simp)]
lemma firstIso_source : T.leftInner.first.j ≫ T.firstIso.hom = T.rightOuter.first.j := by
  let m : T.rightOuter.first.Xbar ⟶ T.first.Xbar := T.rightOuter.middleOpen
  have hm : T.firstIso.hom ≫ m = T.leftInner.middleOpen ≫ T.innerToFirst :=
    T.firstIso_hom_middleOpen
  have hs : T.rightOuter.first.j ≫ m = T.first.j :=
    T.rightOuter.first_j_middleOpen
  have hi : T.leftInner.first.j ≫ T.leftInner.middleOpen =
      T.leftInner.sourceCompactification.j := T.leftInner.first_j_middleOpen
  let : Mono m := inferInstanceAs (Mono T.rightOuter.middleOpen)
  apply (cancel_mono m).1
  rw [Category.assoc, hm, ← Category.assoc, hi, hs]
  exact T.leftInner_j_innerToFirst


/-- Genuine refinement of the first-map compactifications in both routes. -/
def firstRefinement : T.leftInner.first ⟶ T.rightOuter.first where
  hom := T.firstIso.hom
  isProper_hom := inferInstance
  open_fac := T.firstIso_source
  base_fac := T.firstIso_hom_p

end AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition
