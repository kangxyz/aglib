/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.BaseChangeFamilyValue

/-! Axiom guard for the original comparison. -/

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.baseChangeRepresentableBy_homEquiv_of_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.baseChangeRepresentableBy_homEquiv_of_family
