/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.RootCharacters

/-! Axiom guard for the original principal root characters. -/

open AlgebraicGeometry.Scheme.RelativePicard

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.multiplicationKernelRootCharacterEquivOfPrincipalIso'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms multiplicationKernelRootCharacterEquivOfPrincipalIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.multiplicationKernelRootCharacterEquivOfPrincipalIso_apply'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.multiplicationKernelRootCharacterEquivOfPrincipalIso_apply
