/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedAdjointBoundary

/-! Axiom guard for the original Kummer adjunction boundary. -/

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.derivedKummerTriangle_originalAdjunct_boundary'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.derivedKummerTriangle_originalAdjunct_boundary
