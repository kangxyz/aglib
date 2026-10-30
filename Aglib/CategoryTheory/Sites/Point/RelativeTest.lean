/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # Original relative point tests and their germ values

The categorical pullback projections identify the original relative test point.
Native germ naturality then evaluates the same section map at that test; neither
a new point nor a new section functor is selected.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

section Pullback

universe u v

/-- Composition with the original relative test has the specified two point projections. -/
theorem relativeTest_comp_lift {C : Type u} [Category.{v} C] {P U T S : C}
    (a : U ⟶ S) (g : T ⟶ S) [HasPullback a g]
    (b : T ⟶ U) (hb : b ≫ a = g) (η : P ⟶ T) (p : P ⟶ U)
    (hpoint : p ≫ a = η ≫ g) (hp : p = η ≫ b) (t : P ⟶ T) (ht : t = η) :
    t ≫ pullback.lift b (𝟙 T) (hb.trans (Category.id_comp g).symm) =
      pullback.lift p η hpoint := by
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst] using
      (congrArg (fun k => k ≫ b) ht).trans hp.symm
  · simp only [Category.assoc, pullback.lift_snd]
    exact (Category.comp_id t).trans ht

end Pullback

section Germ

universe u v p a b

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{p} J) {A : Type a} [Category.{b} A] [HasColimitsOfSize.{p, p} A]

/-- A proved original point-test equality evaluates the same section followed by its germ. -/
theorem germ_after_test (Q : Cᵒᵖ ⥤ A) {U V : C} {Z : A}
    (a : Z ⟶ Q.obj (op U)) (k : V ⟶ U) (t : Φ.fiber.obj V) (r : Φ.fiber.obj U)
    (hk : Φ.fiber.map k t = r) :
    a ≫ Φ.toPresheafFiber U r Q =
      (a ≫ Q.map k.op) ≫ Φ.toPresheafFiber V t Q := by
  calc
    _ = a ≫ Φ.toPresheafFiber U (Φ.fiber.map k t) Q :=
      congrArg (fun x => a ≫ Φ.toPresheafFiber U x Q) hk.symm
    _ = a ≫ (Q.map k.op ≫ Φ.toPresheafFiber V t Q) :=
      congrArg (fun x => a ≫ x) (Φ.toPresheafFiber_w k t Q).symm
    _ = _ := (Category.assoc _ _ _).symm

end Germ

end CategoryTheory.GrothendieckTopology.Point
