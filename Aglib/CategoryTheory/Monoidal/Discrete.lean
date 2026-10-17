/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The braiding of an additive commutative monoid as a discrete category

Mathlib braids `Discrete M` only for a multiplicative commutative monoid `M`, whose monoidal
structure is `Discrete.monoidal`. For an additive commutative monoid `M`, the additive monoidal
structure `Discrete.addMonoidal` is braided by `add_comm` (`Discrete.addBraidedCategory`) and
symmetric (`Discrete.addSymmetricCategory`). Instance search selects the additive monoidal
structure on `Discrete ℤ`, so these are the braided and symmetric structures found there.
-/

@[expose] public section

universe u

namespace CategoryTheory.Discrete

open MonoidalCategory

variable (M : Type u) [AddCommMonoid M]

/-- The additive discrete monoidal category of an additive commutative monoid, braided by
commutativity. -/
instance addBraidedCategory : BraidedCategory (Discrete M) where
  braiding X Y := Discrete.eqToIso (add_comm X.as Y.as)

/-- The braided additive discrete monoidal category is symmetric. -/
instance addSymmetricCategory : SymmetricCategory (Discrete M) where

end CategoryTheory.Discrete
