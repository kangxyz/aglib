/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Logic.Function.Basic

/-! # Original three-arrow transport without algebra dictionary conversion -/

@[expose] public section

namespace Function

universe u v w z

variable {A : Sort u} {B : Sort v} {C : Sort w} {D : Sort z}

/-- Keep the original arrows and their original carriers; no bundled algebra
structure must be reconstructed at the composite's return boundary. -/
def transportThree (a : A → B) (b : B → C) (c : C → D) : A → D :=
  fun x => c (b (a x))

theorem transportThree_apply (a : A → B) (b : B → C) (c : C → D) (x : A) :
    transportThree a b c x = c (b (a x)) := rfl

theorem transportThree_injective (a : A → B) (b : B → C) (c : C → D)
    (ha : Injective a) (hb : Injective b) (hc : Injective c) :
    Injective (transportThree a b c) := hc.comp (hb.comp ha)

end Function
