/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Point.InitialEvaluation
public import Mathlib.CategoryTheory.Subterminal

/-! # Initial pointed subterminal objects from actual pointed lifts

Cofilteredness equalizes two pointed arrows. A pointed lift back gives a section
because the original object is subterminal, so the two arrows are equal.
The resulting initial object is the original point's actual element.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.GrothendieckTopology.Point

universe u v w a b

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) (T : C) (t : Φ.fiber.obj T)

/-- Pointed lifts from a subterminal object make its original pointed object initial. -/
def isInitialElementsMkOfSubterminal (hT : IsSubterminal T)
    (hlift : ∀ (U : C) (p : Φ.fiber.obj U), ∃ f : T ⟶ U, Φ.fiber.map f t = p) :
    IsInitial (Φ.fiber.elementsMk T t) := by
  classical
  let pointedLift (U : Φ.fiber.Elements) : Φ.fiber.elementsMk T t ⟶ U :=
    Functor.Elements.homMk (Classical.choose (hlift U.obj U.val))
      (Classical.choose_spec (hlift U.obj U.val))
  refine IsInitial.ofUniqueHom pointedLift ?_
  intro U f
  obtain ⟨W, q, hq⟩ := IsCofilteredOrEmpty.cone_maps f (pointedLift U)
  let r := pointedLift W
  have hr : r ≫ q = 𝟙 (Φ.fiber.elementsMk T t) := by
    apply Functor.Elements.hom_ext
    exact hT _ _
  calc
    f = (r ≫ q) ≫ f := by rw [hr, Category.id_comp]
    _ = r ≫ (q ≫ f) := Category.assoc _ _ _
    _ = r ≫ (q ≫ pointedLift U) := congrArg (fun k => r ≫ k) hq
    _ = (r ≫ q) ≫ pointedLift U := (Category.assoc _ _ _).symm
    _ = pointedLift U := by rw [hr, Category.id_comp]

/-- The literal native germ is invertible under the pointed-lift criterion. -/
theorem isIso_toPresheafFiber_of_subterminal {A : Type a} [Category.{b} A]
    [HasColimitsOfSize.{w, w} A] (hT : IsSubterminal T)
    (hlift : ∀ (U : C) (p : Φ.fiber.obj U), ∃ f : T ⟶ U, Φ.fiber.map f t = p)
    (P : Cᵒᵖ ⥤ A) : IsIso (Φ.toPresheafFiber T t P) :=
  Φ.isIso_toPresheafFiber_of_isInitial T t
    (Φ.isInitialElementsMkOfSubterminal T t hT hlift) P

end CategoryTheory.GrothendieckTopology.Point
