/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.SignedCharacterDetection

/-! Axiom guard for the original comparison. -/

/--
info: 'CategoryTheory.Abelian.Ext.eq_character_of_signed_postcomp'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.Ext.eq_character_of_signed_postcomp
