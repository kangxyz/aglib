/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleComposition

/-! # Actual open restrictions in a three-level composition tower -/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition

variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact h] (T : TripleCompactifiedComposition f g h)

/-- The first ambient with its exact factored original source map. -/
def firstOverMiddleOpen :
    DenseCompactification ((f ≫ T.tail.first.j) ≫ T.tail.middleOpen) where
  Xbar := T.first.Xbar
  j := T.first.j
  p := T.first.p
  isOpenImmersion_j := inferInstance
  isProper_p := T.first.toCompactification.isProper_p
  fac := by
    rw [Category.assoc, CompactifiedComposition.first_j_middleOpen]
    exact T.first.fac
  isSchemeTheoreticallyDominant_j := inferInstance

instance tailMiddleOpen_quasiCompact : QuasiCompact T.tail.middleOpen :=
  inferInstanceAs (QuasiCompact (pullback.snd T.last.j T.middle.p))

/-- The inner tower for the first two maps is the actual open restriction. -/
def leftInner : CompactifiedComposition f g where
  targetCompactification := T.tail.first
  sourceCompactification := DenseCompactification.openRestriction
    (f ≫ T.tail.first.j) T.tail.middleOpen T.firstOverMiddleOpen

/-- Its source ambient is literally the pullback along the middle open. -/
def innerToFirst : T.leftInner.sourceCompactification.Xbar ⟶ T.first.Xbar :=
  pullback.snd T.tail.middleOpen T.firstOverMiddleOpen.p

/-- The original source is preserved by the ambient restriction map. -/
@[reassoc (attr := simp)]
lemma leftInner_j_innerToFirst :
    T.leftInner.sourceCompactification.j ≫ T.innerToFirst = T.first.j :=
  DenseCompactification.openRestriction_j_snd
    (f ≫ T.tail.first.j) T.tail.middleOpen T.firstOverMiddleOpen

end AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition
