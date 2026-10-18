/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Flat

/-! Focused consumer of the flatness of polynomial projective space over its base, with axiom
guards. -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

/-- The structure morphism of projective space is flat, by instance. -/
example (R : Type u) [CommRing R] (ι : Type u) : Flat (toSpec R ι) := inferInstance

/--
info: 'AlgebraicGeometry.ProjectiveSpace.flat_coordinateRingCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.flat_coordinateRingCoefficient

/--
info: 'AlgebraicGeometry.ProjectiveSpace.flat_toSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.flat_toSpec
