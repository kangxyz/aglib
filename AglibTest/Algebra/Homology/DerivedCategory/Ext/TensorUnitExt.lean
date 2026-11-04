/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.TensorUnitExt

/-! Axiom guards for the public declarations of this leaf. -/

/--
info: 'CategoryTheory.Abelian.Ext.tensorRightUnitExt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.Ext.tensorRightUnitExt

/--
info: 'CategoryTheory.Abelian.Ext.comp_tensorRightUnitExt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.Ext.comp_tensorRightUnitExt

/--
info: 'CategoryTheory.Abelian.Ext.tensorRightIsoUnitExt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.Ext.tensorRightIsoUnitExt

/--
info: 'CategoryTheory.Abelian.Ext.comp_tensorRightIsoUnitExt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.Ext.comp_tensorRightIsoUnitExt
