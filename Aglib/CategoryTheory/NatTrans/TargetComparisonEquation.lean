/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Category.Basic

/-! # A shared whole-map equation for a compatible map to a fixed target -/
@[expose] public section
namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {X Y T : C}
/-- The unchanged original comparison preserves the specified maps to the target. -/
def TargetComparisonEquation (a : X ⟶ Y) (b : Y ⟶ T) (c : X ⟶ T) : Prop :=
  a ≫ b = c
end CategoryTheory
