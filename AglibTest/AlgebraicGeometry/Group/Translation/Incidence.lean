/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Translation.Incidence

/-! # The full scheme incidence pullback, without reduced-test restrictions -/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open Scheme.Group
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {S : Scheme.{u}} (G : Over S) [GrpObj G] {Z T : Over S}
    (i : Z ⟶ G) (f : T ⟶ G) :
    IsPullback (fst Z T).left (incidenceMorphism G i f).left i.left
      (incidenceDifference G f).left :=
  isPullback_incidenceMorphism G i f

/--
info: 'AlgebraicGeometry.Scheme.Group.isPullback_incidenceMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.isPullback_incidenceMorphism
