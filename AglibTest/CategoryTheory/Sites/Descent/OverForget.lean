/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Sites.Descent.OverForget

/-! Axiom guards for descent over `Over S₀` through the forgetful functor
(`Aglib.CategoryTheory.Sites.Descent.OverForget`). -/

@[expose] public section

/--
info: 'CategoryTheory.Pseudofunctor.isStackFor_restrictAlong_overForget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Pseudofunctor.isStackFor_restrictAlong_overForget

/--
info: 'CategoryTheory.Pseudofunctor.DescentData.fullyFaithfulOfOverFunctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Pseudofunctor.DescentData.fullyFaithfulOfOverFunctor

/--
info: 'CategoryTheory.Pseudofunctor.DescentData.toDescentDataOfOverIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Pseudofunctor.DescentData.toDescentDataOfOverIso
