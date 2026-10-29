/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Insert an original target unit into a functor composite

The complete transformation is constructed over the same variable functors.
Its whole value is the original two-unit composite, and its components are
computed before specializing the categories or functors.
-/

@[expose] public section

namespace CategoryTheory.NatTrans

universe uC vC uD vD

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (L : C ⥤ D) (R : D ⥤ C) (G : D ⥤ D)
  (η : 𝟭 C ⟶ L ⋙ R) (δ : 𝟭 D ⟶ G)

/-- Follow the original unit by the original target unit, using the target's association. -/
def unitInsertion : 𝟭 C ⟶ L ⋙ G ⋙ R :=
  η ≫ Functor.whiskerLeft L (Functor.whiskerRight δ R)

/-- The whole transformation equals the original left-then-right whiskered composite. -/
theorem unitInsertion_eq_original :
    unitInsertion L R G η δ = η ≫ Functor.whiskerRight (Functor.whiskerLeft L δ) R := rfl

/-- The component retains both original factors at their actual objects. -/
theorem unitInsertion_app (K : C) :
    (unitInsertion L R G η δ).app K = η.app K ≫ R.map (δ.app (L.obj K)) := rfl

end CategoryTheory.NatTrans
