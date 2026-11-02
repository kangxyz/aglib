/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange

/-!
# The original bounded exchange test

This predicate retains the original all-degree higher exchange through intrinsic
ordinary right-derived functors. Geometric closure and exact comparison with
any selected derived family use the same predicate.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge

/-- The actual all-degree coefficient test at a specified original square.
This shared predicate keeps the original maps whole during geometric transport. -/
def boundedExchange (n : ℕ) {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) : Prop :=
  ∀ F : AbelianSheaf.{u, u + 1} X, n • 𝟙 F = 0 →
    ∀ q : ℕ, IsIso ((higherBaseChangeMap f f' g g' h q).app F)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
