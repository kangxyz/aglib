/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
# Factorizations through wide pullbacks

A morphism `g : X ⟶ B` factors through the wide pullback of a family `arrows j : objs j ⟶ B` if
and only if it factors through every `arrows j` (`WidePullback.exists_lift_base_iff`), and the
base of a wide pullback of monomorphisms is a monomorphism (`WidePullback.mono_base`). The
consumer is the joint rank stratification of finitely many sheaves,
`AlgebraicGeometry/FlatteningStratification/Finite`.
-/

@[expose] public section

namespace CategoryTheory.Limits.WidePullback

variable {C : Type*} [Category C] {J : Type*} {B : C} {objs : J → C} (arrows : ∀ j, objs j ⟶ B)
  [HasWidePullback B objs arrows]

/-- A morphism to `B` factors through the wide pullback of `arrows` if and only if it factors
through each member of `arrows`. -/
theorem exists_lift_base_iff {X : C} (g : X ⟶ B) :
    (∃ h : X ⟶ widePullback B objs arrows, h ≫ base arrows = g) ↔
      ∀ j, ∃ h : X ⟶ objs j, h ≫ arrows j = g := by
  constructor
  · rintro ⟨h, rfl⟩ j
    exact ⟨h ≫ π arrows j, by rw [Category.assoc, π_arrow]⟩
  · intro H
    choose h hh using H
    exact ⟨lift g h hh, lift_base arrows g h hh⟩

/-- The base of a wide pullback of monomorphisms is a monomorphism. -/
theorem mono_base [∀ j, Mono (arrows j)] : Mono (base arrows) := by
  constructor
  intro X a b hab
  refine hom_ext arrows a b (fun j => ?_) hab
  rw [← cancel_mono (arrows j), Category.assoc, Category.assoc, π_arrow, hab]

end CategoryTheory.Limits.WidePullback
