/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.EqToHom

/-! # Transport of a morphism with its certificate

Transporting the entire certified morphism changes its value by the canonical
target equality morphism. The certificate is transported together with it.
-/

@[expose] public section
namespace CategoryTheory

/-- The value of a transported certified morphism is the original morphism
followed by the canonical target transport. -/
theorem certifiedHomTransport_val {C : Type*} [Category C] {ι : Type*}
    (T : ι → C) (X : C) (P : ∀ i, (X ⟶ T i) → Prop)
    {i j : ι} (h : i = j) (c : {a : X ⟶ T i // P i a}) :
    (Eq.mp (congrArg (fun k => {a : X ⟶ T k // P k a}) h) c).val =
      c.val ≫ eqToHom (congrArg T h) := by
  subst j
  simp

end CategoryTheory
