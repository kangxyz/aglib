/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.FiniteProducts.Smooth

/-! # Smooth relative dimensions of the original variable finite products -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Scheme

universe u

example {S : Scheme.{u}} {n : ℕ} (X : Fin n → Over S) (d : Fin n → ℕ)
    [∀ i, SmoothOfRelativeDimension (d i) (X i).hom] :
    SmoothOfRelativeDimension (∑ i, d i) (finiteProductOver X).hom :=
  smoothOfRelativeDimension_finiteProductOver X d

example {S : Scheme.{u}} (X : Fin 0 → Over S) :
    SmoothOfRelativeDimension 0 (finiteProductOver X).hom := by
  letI : ∀ i : Fin 0, SmoothOfRelativeDimension 0 (X i).hom := fun i => Fin.elim0 i
  simpa using smoothOfRelativeDimension_finiteProductOver X (fun _ => 0)

/--
info: 'AlgebraicGeometry.Scheme.smoothOfRelativeDimension_finiteProductOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.smoothOfRelativeDimension_finiteProductOver
