/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingIntegerUnit

open AlgebraicGeometry.Scheme.EtaleCohomology

/-! Native axiom guard for the original derived integer-source square. -/

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitDerivedIntegerMap_inverseImage'
  depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleUnitDerivedIntegerMap_inverseImage
