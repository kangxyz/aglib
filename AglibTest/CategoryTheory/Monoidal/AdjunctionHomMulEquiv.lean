/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Monoidal.AdjunctionHomMulEquiv

/-! Focused consumer of the multiplicativity of the adjunction bijection on points of monoid
objects, with axiom guards. -/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Monoidal] {M : D} [MonObj M]

/-- The adjunction bijection is an isomorphism of monoids `(L T ⟶ M) ≃* (T ⟶ R M)`. -/
example (T : C) (f g : L.obj T ⟶ M) :
    adj.homMulEquiv T (f * g) = adj.homEquiv T M f * adj.homEquiv T M g ∧
      adj.homEquiv T M 1 = 1 :=
  ⟨map_mul (adj.homMulEquiv T) f g, adj.homEquiv_one T⟩

/-- Its inverse is multiplicative. -/
example {T : C} (f g : T ⟶ R.obj M) :
    (adj.homEquiv T M).symm (f * g) = (adj.homEquiv T M).symm f * (adj.homEquiv T M).symm g :=
  adj.homEquiv_symm_mul f g

/--
info: 'CategoryTheory.Adjunction.homMulEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.homMulEquiv

/--
info: 'CategoryTheory.Adjunction.homEquiv_symm_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.homEquiv_symm_mul
