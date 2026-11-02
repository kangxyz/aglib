/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.FiniteEtaleCompletion

/-! The original cover, its full cartesian square, and its finite boundary. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] (C : FScheme k) (hC : Properties C)
  {U : Scheme.{u}} [Nonempty U] (j : U ⟶ C.left) [IsOpenImmersion j]
  (Y : FiniteEtale U) [ConnectedSpace Y.obj.left] [Surjective Y.obj.hom]

example : ∃ (D : FScheme k) (p : D ⟶ C) (i : Y.obj.left ⟶ D.left),
    Properties D ∧ IsFinite p.left ∧ IsDominant p.left ∧ IsOpenImmersion i ∧
      IsPullback i Y.obj.hom p.left j :=
  exists_finiteEtaleCompletion C hC j Y

example (B : Set C.left) (hBfinite : B.Finite) (hBclosed : IsClosed B)
    (hj : Set.range j = Bᶜ) :
    ∃ (D : FScheme k) (p : D ⟶ C) (i : Y.obj.left ⟶ D.left),
      Properties D ∧ IsFinite p.left ∧ IsDominant p.left ∧ IsOpenImmersion i ∧
        IsPullback i Y.obj.hom p.left j ∧ (p.left ⁻¹' B).Finite ∧
          IsClosed (p.left ⁻¹' B) ∧ Set.range i = (p.left ⁻¹' B)ᶜ :=
  exists_finiteEtaleCompletion_with_boundary C hC j Y B hBfinite hBclosed hj

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.exists_finiteEtaleCompletion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.exists_finiteEtaleCompletion

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.exists_finiteEtaleCompletion_with_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.exists_finiteEtaleCompletion_with_boundary
