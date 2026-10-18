/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Limits.Shapes.WidePullbacks

/-! Focused consumer of factorizations through wide pullbacks, with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-- A morphism factors through a wide pullback of monomorphisms exactly when it factors through
every member, and the base of the wide pullback is a monomorphism. -/
example {C : Type*} [Category C] {J : Type*} {B : C} {objs : J → C} (arrows : ∀ j, objs j ⟶ B)
    [HasWidePullback B objs arrows] [∀ j, Mono (arrows j)] {X : C} (g : X ⟶ B) :
    Mono (WidePullback.base arrows) ∧
      ((∃ h : X ⟶ widePullback B objs arrows, h ≫ WidePullback.base arrows = g) ↔
        ∀ j, ∃ h : X ⟶ objs j, h ≫ arrows j = g) :=
  ⟨WidePullback.mono_base arrows, WidePullback.exists_lift_base_iff arrows g⟩

/--
info: 'CategoryTheory.Limits.WidePullback.exists_lift_base_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Limits.WidePullback.exists_lift_base_iff

/--
info: 'CategoryTheory.Limits.WidePullback.mono_base' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Limits.WidePullback.mono_base
