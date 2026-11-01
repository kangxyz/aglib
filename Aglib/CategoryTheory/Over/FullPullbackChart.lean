/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Actual maps from entire pullback charts

An original Cartesian square and an actual Over-isomorphism construct the map
from the entire composite pullback into the supplied source chart. Both the
chosen pullbacks and its original source projection are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Over

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {Y X Y' X' T W : C}
  (f : Y ⟶ X) (j : X' ⟶ X) (u : Y' ⟶ Y) (f' : Y' ⟶ X')
  (H : IsPullback u f' f j) (q : T ⟶ X') (w : W ⟶ Y)
  (e : (Over.pullback f').obj (Over.mk q) ≅ (Over.pullback u).obj (Over.mk w))

/-- The entire original pullback chart maps into the actual source chart. -/
def fullPullbackChartMap : Limits.pullback f (q ≫ j) ⟶ W :=
  let a : Limits.pullback f (q ≫ j) ⟶ Y' :=
    H.lift (Limits.pullback.fst f (q ≫ j)) (Limits.pullback.snd f (q ≫ j) ≫ q)
      (by simpa only [Category.assoc] using Limits.pullback.condition (f := f) (g := q ≫ j))
  let b : Limits.pullback f (q ≫ j) ⟶ Limits.pullback q f' :=
    Limits.pullback.lift (Limits.pullback.snd f (q ≫ j)) a (by simp [a])
  b ≫ e.hom.left ≫ Limits.pullback.fst w u

/-- The full-chart map retains the original coefficient map to the source. -/
@[reassoc]
theorem fullPullbackChartMap_over :
    fullPullbackChartMap f j u f' H q w e ≫ w = Limits.pullback.fst f (q ≫ j) := by
  let a : Limits.pullback f (q ≫ j) ⟶ Y' :=
    H.lift (Limits.pullback.fst f (q ≫ j)) (Limits.pullback.snd f (q ≫ j) ≫ q)
      (by simpa only [Category.assoc] using Limits.pullback.condition (f := f) (g := q ≫ j))
  let b : Limits.pullback f (q ≫ j) ⟶ Limits.pullback q f' :=
    Limits.pullback.lift (Limits.pullback.snd f (q ≫ j)) a (by simp [a])
  have he : e.hom.left ≫ Limits.pullback.snd w u = Limits.pullback.snd q f' := e.hom.w
  have hb : b ≫ Limits.pullback.snd q f' = a := Limits.pullback.lift_snd _ _ _
  have ha : a ≫ u = Limits.pullback.fst f (q ≫ j) := H.lift_fst _ _ _
  change (b ≫ e.hom.left ≫ Limits.pullback.fst w u) ≫ w = _
  calc
    (b ≫ e.hom.left ≫ Limits.pullback.fst w u) ≫ w =
        b ≫ e.hom.left ≫ Limits.pullback.snd w u ≫ u := by
      simpa only [Category.assoc] using congrArg (fun z => b ≫ e.hom.left ≫ z)
        (Limits.pullback.condition (f := w) (g := u))
    _ = (b ≫ Limits.pullback.snd q f') ≫ u := by
      simpa only [Category.assoc] using congrArg (fun z => b ≫ z ≫ u) he
    _ = Limits.pullback.fst f (q ≫ j) := (congrArg (fun z => z ≫ u) hb).trans ha

end CategoryTheory.Over
