/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.GradedProduct

/-! Axiom guard for the original ordered graded Ext product. -/

open CategoryTheory.Abelian.Ext

/--
info: 'CategoryTheory.Abelian.Ext.bijective_orderedProduct_of_graded_components'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bijective_orderedProduct_of_graded_components
