/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Group.Hom.FiniteExact

/-! Original additive exact pairs at independent carrier universes. -/

@[expose] public section

universe u v w

example {A : Type u} {B : Type v} {C : Type w}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Finite A] [Finite C]
    (f : A →+ B) (g : B →+ C) (hfg : Function.Exact f g) : Finite B :=
  AddMonoidHom.finite_of_exact f g hfg

/-- info: 'AddMonoidHom.finite_of_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AddMonoidHom.finite_of_exact
