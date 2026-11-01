/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.GenericPoint

/-! # The original integral stalk zero prime and scheme generic point -/

@[expose] public section

open AlgebraicGeometry

universe u

example {C : Scheme.{u}} [IsIntegral C] (c : C) :
    C.fromSpecStalk c (⊥ : PrimeSpectrum (C.presheaf.stalk c)) = genericPoint C :=
  Scheme.fromSpecStalk_bot c

/--
info: 'AlgebraicGeometry.Scheme.fromSpecStalk_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.fromSpecStalk_bot
