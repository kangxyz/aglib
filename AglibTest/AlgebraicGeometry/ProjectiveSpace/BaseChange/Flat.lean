/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Flat

/-! Focused consumer of the flatness of coefficient base change of projective space. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

/-- The projection of a field extension is flat, as an instance. -/
example (k K : Type u) [Field k] [Field K] [Algebra k K] (ι : Type u) :
    Flat (ProjectiveSpace.map (algebraMap k K) ι) :=
  inferInstance

/--
info: 'AlgebraicGeometry.ProjectiveSpace.flat_map'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.flat_map

/--
info: 'AlgebraicGeometry.ProjectiveSpace.flat_map_algebraMap'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.flat_map_algebraMap
