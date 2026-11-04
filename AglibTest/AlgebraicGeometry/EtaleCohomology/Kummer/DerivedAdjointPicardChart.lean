/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedAdjointPicardChart

open AlgebraicGeometry.Scheme.EtaleCohomology.Picard

/-! Native axiom guards for the original normalized Picard terminal-chart interface. -/

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Picard.gmHigherDirectImageNormalizedPicardIso_terminalValue'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gmHigherDirectImageNormalizedPicardIso_terminalValue

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Picard.gmDerivedAdjunct_h1_of_terminalValue'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gmDerivedAdjunct_h1_of_terminalValue
