/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Original scalars on an opposite category

The actual unop map transports the original module structure on morphisms.
The resulting native Linear structure is explicit, rather than a new global
instance. Consumers can install this same structure locally.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Linear

/-- The native opposite category carries the original scalars through the
actual unop map on morphisms. -/
@[instance_reducible]
def opposite (R : Type*) [Semiring R] (C : Type*) [Category* C]
    [Preadditive C] [Linear R C] : Linear R Cᵒᵖ where
  homModule X Y :=
    (show (X ⟶ Y) ≃+ (Y.unop ⟶ X.unop) from
      { toFun := Quiver.Hom.unop
        invFun := Quiver.Hom.op
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }).module R
  smul_comp X Y Z r f g := by
    apply Quiver.Hom.unop_inj
    exact Linear.comp_smul Z.unop Y.unop X.unop g.unop r f.unop
  comp_smul X Y Z f r g := by
    apply Quiver.Hom.unop_inj
    exact Linear.smul_comp Z.unop Y.unop X.unop r g.unop f.unop

end CategoryTheory.Linear
