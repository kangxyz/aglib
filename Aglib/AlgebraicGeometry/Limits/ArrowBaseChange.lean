/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Induced arrows over cartesian base-change squares

Relocated from R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Existing mathematical declarations and explicit source boundaries are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.ArrowBaseChange` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`d1cff238c4354e815ea4edbe5de9a159b1317b1dc953f0cb4945b41a4f12bbcd`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Pullback.ArrowBaseChange

/-- The actual induced arrow over a cartesian field/base square is a pullback. -/
theorem arrowBaseChange_isPullback {C Y A B A' B' : Scheme.{u}}
    (j : C ⟶ Y) (e : C ⟶ A) (π : Y ⟶ B) (t : A ⟶ B)
    (h : j ≫ π = e ≫ t) (f : A' ⟶ A) (b : B' ⟶ B) (t' : A' ⟶ B')
    (hb : IsPullback t' f b t) (a : pullback e f ⟶ pullback π b)
    (ha₁ : a ≫ pullback.fst π b = pullback.fst e f ≫ j)
    (ha₂ : a ≫ pullback.snd π b = pullback.snd e f ≫ t') :
    IsPullback (pullback.fst e f) a j (pullback.fst π b) := by
  apply IsPullback.flip
  apply IsPullback.of_right _ ha₁ (IsPullback.of_hasPullback π b).flip
  rw [ha₂, h]
  exact (IsPullback.of_hasPullback e f).flip.paste_horiz hb

end AlgebraicGeometry.Scheme.Pullback.ArrowBaseChange
