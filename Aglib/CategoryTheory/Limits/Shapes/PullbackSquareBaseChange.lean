/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Base change of an original Cartesian square

The original two pullbacks are retained, including both projections of their
comparison map. No replacement realization of either pullback is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.IsPullback

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {E D U V X S : C} {b : E ⟶ D} {p : E ⟶ U} {g : D ⟶ X} {j : U ⟶ X}
  {t : V ⟶ U} {jS : V ⟶ S} {s : S ⟶ X}
  (H : IsPullback b p g j) (K : IsPullback t jS j s)

/-- The canonical map between the original base-changed objects of a square. -/
def baseChangeSquareMap : pullback p t ⟶ pullback g s :=
  pullback.lift (pullback.fst p t ≫ b) (pullback.snd p t ≫ jS) (by
    rw [Category.assoc, H.w, ← Category.assoc, pullback.condition,
      Category.assoc, K.w, Category.assoc])

@[reassoc (attr := simp)] theorem baseChangeSquareMap_fst :
    baseChangeSquareMap H K ≫ pullback.fst g s = pullback.fst p t ≫ b :=
  pullback.lift_fst ..

@[reassoc (attr := simp)] theorem baseChangeSquareMap_snd :
    baseChangeSquareMap H K ≫ pullback.snd g s = pullback.snd p t ≫ jS :=
  pullback.lift_snd ..

/-- Base changing the original square preserves its Cartesian property. -/
theorem baseChangeSquareMap_isPullback :
    IsPullback (baseChangeSquareMap H K) (pullback.snd p t)
      (pullback.snd g s) jS := by
  apply IsPullback.of_right (h₁₂ := pullback.fst g s) (h₂₂ := s)
    _ (baseChangeSquareMap_snd H K) (IsPullback.of_hasPullback g s)
  rw [baseChangeSquareMap_fst, ← K.w]
  exact (IsPullback.of_hasPullback p t).paste_horiz H

end CategoryTheory.IsPullback
