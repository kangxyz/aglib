/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.TripleCompositionFirst

/-! # The original third Cartesian square in triple composition -/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition
variable {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
  [QuasiCompact h] (T : TripleCompactifiedComposition f g h)

instance innerToFirst_isOpenImmersion : IsOpenImmersion T.innerToFirst :=
  inferInstanceAs (IsOpenImmersion (pullback.snd T.tail.middleOpen T.firstOverMiddleOpen.p))

/-- The intermediate ambient restriction retains its original Cartesian square. -/
theorem isPullback_innerToFirst :
    IsPullback T.leftInner.sourceCompactification.p T.innerToFirst
      T.tail.middleOpen T.first.p :=
  (DenseCompactification.isPullback_openRestriction
    (f ≫ T.tail.first.j) T.tail.middleOpen T.firstOverMiddleOpen).flip

end AlgebraicGeometry.Scheme.Hom.TripleCompactifiedComposition
