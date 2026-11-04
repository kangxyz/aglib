/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCoefficientIdentity

/-! Axiom guards for the original coefficient identities. -/

open AlgebraicGeometry.Scheme.EtaleCohomology

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitInverseImageIso_identity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleUnitInverseImageIso_identity

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleRootsOfUnityInverseImageIso_identity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleRootsOfUnityInverseImageIso_identity
