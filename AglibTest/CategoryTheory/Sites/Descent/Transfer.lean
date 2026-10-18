/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Sites.Descent.Transfer

/-! Axiom guards for the transfer of descent data along a transformation of pseudofunctors
(`Aglib.CategoryTheory.Sites.Descent.Transfer`). -/

@[expose] public section

/--
info: 'CategoryTheory.Pseudofunctor.CompTrans.exists_descentData_iso_of_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Pseudofunctor.CompTrans.exists_descentData_iso_of_bijective
