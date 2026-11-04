/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.UniversalProperty.Functoriality

/-! # Axiom guards for the original character functoriality -/

@[expose] public section

open AlgebraicGeometry.Scheme.Group.CartierDuality

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.characterOfPoint_dualMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms characterOfPoint_dualMap

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.characterEquiv_dualMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms characterEquiv_dualMap
