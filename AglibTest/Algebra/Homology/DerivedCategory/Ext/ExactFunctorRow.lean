/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ExactFunctorRow

/-! Axiom guard for the signed interchange of an original natural exact row. -/

/--
info: 'CategoryTheory.Functor.exactFunctorRow_extClass_left'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.exactFunctorRow_extClass_left
