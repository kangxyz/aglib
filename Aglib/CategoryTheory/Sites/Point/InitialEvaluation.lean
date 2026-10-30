/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Evaluation at an initial pointed object

An initial object of the original point's elements category gives an invertible
literal germ map. Naturality of that germ and the original sheafification unit
then make sheafification invertible at the same object.
-/

@[expose] public noncomputable section

universe p u v a b

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{p} J) {A : Type a} [Category.{b} A]
  [HasColimitsOfSize.{p, p} A] (T : C) (t : Φ.fiber.obj T)
  (ht : IsInitial (Φ.fiber.elementsMk T t))

include ht

/-- An initial pointed object makes the original germ into the point colimit
an isomorphism for every presheaf. -/
theorem isIso_toPresheafFiber_of_isInitial (P : Cᵒᵖ ⥤ A) :
    IsIso (Φ.toPresheafFiber T t P) :=
  isIso_ι_of_isTerminal ht.op ((Functor.Elements.π Φ.fiber).op ⋙ P)

/-- Original sheafification preserves evaluation at an initial pointed object. -/
theorem isIso_toSheafify_app_of_isInitial [HasProducts.{p} A] [HasWeakSheafify J A]
    (P : Cᵒᵖ ⥤ A) : IsIso ((CategoryTheory.toSheafify J P).app (op T)) := by
  let Q : Cᵒᵖ ⥤ A := CategoryTheory.sheafify J P
  let η : P ⟶ Q := CategoryTheory.toSheafify J P
  let : IsIso (Φ.toPresheafFiber T t P) :=
    Φ.isIso_toPresheafFiber_of_isInitial T t ht P
  let : IsIso (Φ.toPresheafFiber T t Q) :=
    Φ.isIso_toPresheafFiber_of_isInitial T t ht Q
  let : IsIso ((Φ.presheafFiber (A := A)).map η) := by
    change IsIso ((Φ.presheafFiber (A := A)).map (CategoryTheory.toSheafify J P))
    infer_instance
  have h : IsIso (η.app (op T) ≫ Φ.toPresheafFiber T t Q) := by
    rw [← Φ.toPresheafFiber_naturality (A := A) η T t]
    infer_instance
  exact IsIso.of_isIso_comp_right (η.app (op T)) (Φ.toPresheafFiber T t Q)

end CategoryTheory.GrothendieckTopology.Point
