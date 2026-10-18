/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Sites.Descent.Bind

/-! Axiom guards for `pullHom` along equal morphisms and the compatibility criterion for descent
morphisms (`Aglib.CategoryTheory.Sites.Descent.Bind`). -/

@[expose] public section

/--
info: 'CategoryTheory.Pseudofunctor.toDescentData_comm_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Pseudofunctor.toDescentData_comm_iff

/--
info: 'CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_congr_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_congr_left
