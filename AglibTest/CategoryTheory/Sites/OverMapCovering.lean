/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Sites.OverMapCovering

/-! Focused consumer of the correspondence of coverings along `Over.map`, with axiom guards. -/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)

/-- A sieve on `U : Over X` covers if and only if its image under `Over.map f` covers. -/
example {U : Over X} (R : Sieve U) :
    R.functorPushforward (Over.map f) ∈ J.over Y ((Over.map f).obj U) ↔ R ∈ J.over X U :=
  J.functorPushforward_over_map_mem_iff f R

/-- A sieve on `(Over.map f).obj U` covers if and only if its preimage under `Over.map f` covers;
the forward direction is the cover-lifting property of `Over.map f`. -/
example {U : Over X} (R : Sieve ((Over.map f).obj U)) (hR : R ∈ J.over Y ((Over.map f).obj U)) :
    R.functorPullback (Over.map f) ∈ J.over X U :=
  (J.functorPullback_over_map_mem_iff f R).mpr hR

/--
info: 'CategoryTheory.GrothendieckTopology.functorPushforward_over_map_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.functorPushforward_over_map_mem_iff

/--
info: 'CategoryTheory.GrothendieckTopology.functorPullback_over_map_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.functorPullback_over_map_mem_iff
