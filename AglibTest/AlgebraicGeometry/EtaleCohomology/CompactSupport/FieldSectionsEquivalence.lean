/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldSectionsEquivalence

/-! Axiom guard for the original sections equivalence. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients.moduleFieldSectionsEquivalence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms moduleFieldSectionsEquivalence
