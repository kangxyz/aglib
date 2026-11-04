/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.FrameClass

/-! Axiom guards for the original Weil family coefficient and class comparisons. -/

open AlgebraicGeometry.Scheme.RelativePicard

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.representedSheafMap_multiplicationFamilyRootCharacter_comp_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms representedSheafMap_multiplicationFamilyRootCharacter_comp_inclusion

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.multiplicationFamilyKummerClass_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms multiplicationFamilyKummerClass_inclusion

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.neg_multiplicationFamilyKummerClass_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms neg_multiplicationFamilyKummerClass_inclusion
