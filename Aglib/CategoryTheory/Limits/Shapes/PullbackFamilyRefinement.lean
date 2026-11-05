/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # A target-stage refinement on an arbitrary family

An original map from a base-changed target stage to a target chart induces a
map from the directly base-changed family to that chart's original pullback.
Both projection laws hold for the native pullback maps. No Cartesian-square
certificate, invertibility, or chosen comparison is an extra input.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] {S X W T U : C}
  (t : T ⟶ S) (f : X ⟶ S) (p : W ⟶ X) (a : U ⟶ X)
  [HasPullback t f] [HasPullback t (p ≫ f)] [HasPullback a p]
  (b : pullback t f ⟶ U) (hb : b ≫ a = pullback.snd t f)

/-- The canonical map on the family induced by a target-stage refinement.
Its source is the direct base change along `p ≫ f`, not a replacement stage. -/
def pullback.familyRefinement : pullback t (p ≫ f) ⟶ pullback a p :=
  pullback.lift
    (pullback.map t (p ≫ f) t f (𝟙 T) p (𝟙 S) (by simp) (by simp) ≫ b)
    (pullback.snd t (p ≫ f))
    (by
      rw [Category.assoc, hb]
      exact pullback.lift_snd _ _ _)

/-- The chart projection is the original target-stage map after the original
map from the directly base-changed family. -/
@[reassoc (attr := simp)]
theorem pullback.familyRefinement_fst :
    pullback.familyRefinement t f p a b hb ≫ pullback.fst a p =
      pullback.map t (p ≫ f) t f (𝟙 T) p (𝟙 S) (by simp) (by simp) ≫ b :=
  pullback.lift_fst _ _ _

/-- The family projection is the original direct target-stage projection. -/
@[reassoc (attr := simp)]
theorem pullback.familyRefinement_snd :
    pullback.familyRefinement t f p a b hb ≫ pullback.snd a p =
      pullback.snd t (p ≫ f) :=
  pullback.lift_snd _ _ _

end CategoryTheory.Limits
