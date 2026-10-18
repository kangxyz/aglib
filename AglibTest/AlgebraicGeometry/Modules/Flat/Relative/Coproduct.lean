/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Coproduct

/-! Focused consumer of the relative flatness of coproducts, with an axiom guard. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

/-- A coproduct of two relatively flat modules is relatively flat. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : X.Modules) (hM : relativeFlat f M)
    (hN : relativeFlat f N) :
    relativeFlat f (∐ fun b : ULift.{u} Bool => if b.down then M else N) :=
  relativeFlat_coproduct f _ fun b => by
    cases b with
    | up b => cases b <;> simpa

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_coproduct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_coproduct
