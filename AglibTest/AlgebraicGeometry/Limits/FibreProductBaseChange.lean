/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Limits.FibreProductBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! Focused consumer of the base-change square of the second factor of a fibre product, with an
axiom guard. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- The square of `pullback.map p g' p g (𝟙 X) f (𝟙 S)` over `f` is cartesian, so properness of
`X ×_S T ⟶ T` passes to `X ×_S T' ⟶ T'`. -/
example {X S T T' : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S) (f : T' ⟶ T)
    (hp : IsProper (pullback.snd p g)) : IsProper (pullback.snd p (f ≫ g)) :=
  MorphismProperty.of_isPullback (Scheme.isPullback_pullbackMap_snd p g (f ≫ g) f rfl) hp

/--
info: 'AlgebraicGeometry.Scheme.isPullback_pullbackMap_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isPullback_pullbackMap_snd
