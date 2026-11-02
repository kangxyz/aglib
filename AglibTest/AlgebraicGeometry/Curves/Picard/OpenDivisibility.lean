/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.OpenDivisibility

/-! Divisibility on the actual open Picard group, with level one retained. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]

/-- The omitted point is an existence hypothesis, not a selected origin in the interface. -/
example (hx : ∃ x : X.left, IsClosed ({x} : Set X.left) ∧ x ∉ Set.range j)
    (n : ℕ) (hn : IsUnit (n : k)) (c : PicardGroup U) : ∃ b : PicardGroup U, n • b = c :=
  Curve.exists_nsmul_eq_of_isOpenImmersion hX j n hn hx c

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.exists_nsmul_eq_of_isOpenImmersion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.exists_nsmul_eq_of_isOpenImmersion
