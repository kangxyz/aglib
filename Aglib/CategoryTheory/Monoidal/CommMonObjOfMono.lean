/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-! # Commutativity reflected by a monic monoid morphism -/

@[expose] public section

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory

universe v u

/-- A monic monoid morphism into a commutative monoid object reflects the
entire commutativity equation, with the original monoid structures unchanged. -/
theorem IsCommMonObj.of_mono {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] {G H : C} [MonObj G] [MonObj H] [IsCommMonObj G]
    (j : H ⟶ G) [Mono j] [IsMonHom j] : IsCommMonObj H where
  mul_comm := by
    rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom,
      ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]

end CategoryTheory
