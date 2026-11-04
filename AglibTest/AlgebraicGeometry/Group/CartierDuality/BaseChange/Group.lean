/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.BaseChange.Group

/-! # Axiom guards for the original Cartier comparison laws -/

@[expose] public section

open AlgebraicGeometry.Scheme.Group.CartierDuality

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.characterEquivBaseChange_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms characterEquivBaseChange_mul

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.dualGroupBaseChangeOverIso_comp_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dualGroupBaseChangeOverIso_comp_mul

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.dualGroupBaseChangeOverIso_comp_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dualGroupBaseChangeOverIso_comp_one

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.dualGroupBaseChangeOverIso_isMonHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dualGroupBaseChangeOverIso_isMonHom

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.dualGroupBaseChangeIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dualGroupBaseChangeIso

/--
info: 'AlgebraicGeometry.Scheme.Group.CartierDuality.dualGroupBaseChangeIso_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dualGroupBaseChangeIso_hom
