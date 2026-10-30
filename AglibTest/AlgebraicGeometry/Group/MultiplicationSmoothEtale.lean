/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicationSmoothEtale

/-! # Invertible multiplication needs smoothness and the native commutative law -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Group.Multiplication

universe u

example {k : Type u} [Field k] (G : Grp (FScheme k))
    [Smooth G.X.hom] [IsCommMonObj G.X] (n : ℕ) (hn : IsUnit (n : k)) :
    Etale ((𝟙 G.X) ^ n).left :=
  multiplication_etale_of_smooth_of_isUnit G n hn

/--
info: 'AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_etale_of_smooth_of_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_etale_of_smooth_of_isUnit
