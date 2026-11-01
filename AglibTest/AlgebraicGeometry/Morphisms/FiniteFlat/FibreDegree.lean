/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.FibreDegree

/-! # Actual finite-flat fibre degree, including nonreduced fibres -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom Scheme.Hom.FiniteFlat

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]

example (K : Type u) [Field K] (p : Spec (.of K) ⟶ Y) :
    finiteSchemeDegree K (pullback.snd f p) = f.finrank (p default) :=
  finiteSchemeDegree_fibre_eq_finrank f K p

variable [IsIntegral X] [IsIntegral Y] [IsDominant f]
  [LocallyOfFinitePresentation f]

example (K : Type u) [Field K] (p : Spec (.of K) ⟶ Y) :
    finiteSchemeDegree K (pullback.snd f p) = functionFieldDegree f :=
  finiteSchemeDegree_fibre_eq_functionFieldDegree f K p

example (h : functionFieldDegree f = 1) : IsIso f :=
  isIso_of_functionFieldDegree_eq_one f h

/--
info: 'AlgebraicGeometry.Scheme.Hom.FiniteFlat.finiteSchemeDegree_fibre_eq_functionFieldDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.FiniteFlat.finiteSchemeDegree_fibre_eq_functionFieldDegree

/--
info: 'AlgebraicGeometry.Scheme.Hom.FiniteFlat.isIso_of_functionFieldDegree_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.FiniteFlat.isIso_of_functionFieldDegree_eq_one
