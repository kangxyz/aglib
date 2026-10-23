/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Actual geometric fibre points in a specified cartesian square -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A specified cartesian square gives the actual bijection on points over a
fixed base point, by its universal property and original projections. -/
def cartesianPointOverEquiv {C : Type*} [Category* C] {T X Y Z P : C}
    (a : T ⟶ X) (b : T ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback a b f g) (p : P ⟶ Y) :
    {t : P ⟶ T // t ≫ b = p} ≃ {x : P ⟶ X // x ≫ f = p ≫ g} where
  toFun t := ⟨t.val ≫ a, by
    rw [Category.assoc, h.w, ← Category.assoc, t.property]⟩
  invFun x := ⟨h.lift x.val p x.property, h.lift_snd _ _ _⟩
  left_inv t := by
    apply Subtype.ext
    apply h.hom_ext
    · exact h.lift_fst _ _ _
    · exact (h.lift_snd _ _ _).trans t.property.symm
  right_inv x := Subtype.ext (h.lift_fst _ _ _)

end CategoryTheory
