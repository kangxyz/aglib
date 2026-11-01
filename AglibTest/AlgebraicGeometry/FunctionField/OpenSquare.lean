/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.OpenSquare

/-! Native open-field maps and approved-axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.FunctionField

universe u
variable {V U Y X : Scheme.{u}}
  [IsIntegral V] [IsIntegral U] [IsIntegral Y] [IsIntegral X]
  (p : Y ⟶ X) [IsDominant p] (f : V ⟶ U) [IsDominant f]
  (jU : U ⟶ X) [IsOpenImmersion jU] (jV : V ⟶ Y) [IsOpenImmersion jV]
  (h : f ≫ jU = jV ≫ p)

/-- The original field square requires commutativity, without a Cartesian or finite premise. -/
example : (functionFieldMap f).comp (fieldEquiv jU).toRingHom =
    (fieldEquiv jV).toRingHom.comp (functionFieldMap p) := map_open_square p f jU jV h

/-- info: 'AlgebraicGeometry.Scheme.FunctionField.map_open_square' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.FunctionField.map_open_square

/-- info: 'AlgebraicGeometry.Scheme.FunctionField.map_open_square_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.FunctionField.map_open_square_inv

/-- info: 'AlgebraicGeometry.Scheme.FunctionField.finrank_open_square' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.FunctionField.finrank_open_square

/-- info: 'AlgebraicGeometry.Scheme.FunctionField.finite_of_open_square' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.FunctionField.finite_of_open_square
