/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionRestriction

/-! # The original pullback-pasting comparison for triple composition -/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition

variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact h] (T : TripleCompactifiedComposition f g h)

/-- The two successive open-restriction squares paste to the original outer square. -/
theorem isPullback_leftInner :
    IsPullback T.innerToFirst T.leftInner.composite.p
      T.leftOuter.sourceCompactification.p T.last.j :=
  (DenseCompactification.isPullback_openRestriction
    (f ≫ T.tail.first.j) T.tail.middleOpen T.firstOverMiddleOpen).paste_vert
    T.tail.isPullback_middleOpen

/-- The left-associated intermediate ambients are identified by the actual pullback cone. -/
def leftIntermediateIso :
    T.leftInner.composite.Xbar ≅ T.leftOuter.first.Xbar :=
  T.isPullback_leftInner.flip.isoPullback

/-- The comparison preserves the original structural projection exactly. -/
@[reassoc (attr := simp)]
lemma leftIntermediateIso_hom_p :
    T.leftIntermediateIso.hom ≫ T.leftOuter.first.p = T.leftInner.composite.p :=
  T.isPullback_leftInner.flip.isoPullback_hom_fst

/-- The comparison retains the original ambient open projection. -/
@[reassoc (attr := simp)]
lemma leftIntermediateIso_hom_middleOpen :
    T.leftIntermediateIso.hom ≫ T.leftOuter.middleOpen = T.innerToFirst :=
  T.isPullback_leftInner.flip.isoPullback_hom_snd

end AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition
