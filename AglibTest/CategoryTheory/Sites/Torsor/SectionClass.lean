/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.SectionClass

/-! Axiom guard for the original comparison. -/

open CategoryTheory.Sheaf

/--
info: 'CategoryTheory.Sheaf.torsorExtClass_of_extensionLift_of_section'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms torsorExtClass_of_extensionLift_of_section
