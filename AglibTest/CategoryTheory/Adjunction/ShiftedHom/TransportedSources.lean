/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.ShiftedHom.TransportedSources

/-! Axiom guard for the original comparison. -/

/--
info: 'CategoryTheory.shiftedHomEquiv_of_mate_of_transported_sources'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.shiftedHomEquiv_of_mate_of_transported_sources
