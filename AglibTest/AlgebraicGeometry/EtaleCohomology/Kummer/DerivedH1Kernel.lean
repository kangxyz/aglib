/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedH1Kernel

open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

/-! Axiom guards for the original derived Kummer row and represented scheme torsion. -/

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.derivedKummerH1KernelIso'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms derivedKummerH1KernelIso

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.derivedKummerH1KernelIso_inclusion'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms derivedKummerH1KernelIso_inclusion

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.derivedKummerH1KernelIso_power'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms derivedKummerH1KernelIso_power

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.representedMultiplicationFiberH1Iso_hom_inclusion'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms representedMultiplicationFiberH1Iso_hom_inclusion
