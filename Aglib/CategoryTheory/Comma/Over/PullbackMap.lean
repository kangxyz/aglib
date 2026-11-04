/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! The original base change of an over-category map is Cartesian. -/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.Over

/-- The actual map under the original pullback functor, with its original
first projections, gives a Cartesian square in the ambient category. -/
theorem isPullback_map_left {C : Type u} [Category.{v} C] {S T : C}
    (g : T ⟶ S) [HasPullbacksAlong g] {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom g) ((Over.pullback g).map f).left
      f.left (pullback.fst Y.hom g) := by
  let H₀ := IsPullback.of_hasPullback Y.hom g
  have H : IsPullback (pullback.fst X.hom g) (pullback.snd X.hom g)
      (f.left ≫ Y.hom) g := by
    rw [Over.w f]
    exact IsPullback.of_hasPullback X.hom g
  let a := H₀.lift (pullback.fst X.hom g ≫ f.left) (pullback.snd X.hom g)
    (by rw [Category.assoc, Over.w f, pullback.condition])
  have H₁ : IsPullback (pullback.fst X.hom g) a f.left (pullback.fst Y.hom g) :=
    IsPullback.of_bot' H H₀
  have ha : a = ((Over.pullback g).map f).left := by
    change a = pullback.lift (pullback.fst X.hom g ≫ f.left) (pullback.snd X.hom g)
      (by rw [Category.assoc, Over.w f, pullback.condition])
    apply H₀.hom_ext
    · rw [H₀.lift_fst, pullback.lift_fst]
    · rw [H₀.lift_snd, pullback.lift_snd]
  exact ha ▸ H₁

end CategoryTheory.Over
