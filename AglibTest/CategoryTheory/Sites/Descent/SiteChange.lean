/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Sites.Descent.SiteChange

/-! Axiom guards for whiskering a pseudofunctor by a natural transformation
(`Aglib.CategoryTheory.Sites.Descent.SiteChange`). -/

@[expose] public section

/--
info: 'CategoryTheory.Pseudofunctor.mapComp'_paste_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Pseudofunctor.mapComp'_paste_app

/--
info: 'CategoryTheory.Pseudofunctor.CompTrans.ofNatTrans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CategoryTheory.Pseudofunctor.CompTrans.ofNatTrans
