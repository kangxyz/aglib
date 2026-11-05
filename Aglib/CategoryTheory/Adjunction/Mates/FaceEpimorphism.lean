/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Category.Basic

/-! # Epimorphism transport through an original commuting face

Only the source restriction and the comparison at its target need be epic.
The other comparison is not required to be invertible or epic.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- A commuting face transports epimorphy without inverting either comparison. -/
theorem epi_of_commuting_face {A B A' B' : C}
    {r : A ⟶ B} {b : B ⟶ B'} {a : A ⟶ A'} {r' : A' ⟶ B'}
    (h : r ≫ b = a ≫ r') (hr : Epi r) (hb : Epi b) : Epi r' := by
  let : Epi (r ≫ b) := epi_comp' hr hb
  exact epi_of_epi_fac h.symm

end CategoryTheory
