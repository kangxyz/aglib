/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.IdealSheaf.EmptySubscheme

/-! Focused consumer of the empty closed subscheme: a closed subscheme is empty, and its structure
module is zero, exactly for the unit ideal sheaf, with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/-- The unit ideal sheaf cuts out a closed subscheme with zero structure module. -/
example {X : Scheme.{u}} : IsZero (⊤ : X.IdealSheafData).quotientModule :=
  (Scheme.IdealSheafData.isZero_quotientModule_iff ⊤).mpr rfl

/-- A closed subscheme with a point has a nonzero structure module. -/
example {X : Scheme.{u}} (W : X.IdealSheafData) (w : W.subscheme) : ¬IsZero W.quotientModule :=
  fun h => isEmpty_iff.mp (W.isEmpty_subscheme_of_isZero_quotientModule h) w

example {X : Scheme.{u}} (W : X.IdealSheafData) : Nonempty W.subscheme ↔ W ≠ ⊤ :=
  W.nonempty_subscheme_iff

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.isZero_quotientModule_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.isZero_quotientModule_iff

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.isEmpty_subscheme_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.isEmpty_subscheme_iff
