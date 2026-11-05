/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.Category

/-! # Whole naturality from a specified component factorization -/

@[expose] public section

namespace CategoryTheory

universe uC vC uD vD

/-- Preserve given component arrows while deriving their whole naturality from
an actual factorization through two existing natural transformations. -/
def natTransOfComponentFactorization
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
    (k : ∀ c, F.obj c ⟶ H.obj c)
    (hk : ∀ c, k c = a.app c ≫ b.app c) : F ⟶ H where
  app := k
  naturality c d f := by
    rw [hk c, hk d]
    exact (a ≫ b).naturality f

end CategoryTheory
