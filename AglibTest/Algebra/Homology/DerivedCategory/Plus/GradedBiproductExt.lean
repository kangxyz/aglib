/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.GradedBiproductExt

/-! Axiom guards for the original comparison. -/

open CategoryTheory.Abelian.Ext

/--
info: 'CategoryTheory.Abelian.Ext.plusUnitGradedBiproductExtAddEquiv_injection'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms plusUnitGradedBiproductExtAddEquiv_injection
