/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ObjectProperty.EquivalenceRelation

/-!
# Equivalence relations tested on the objects of a property

The declarations below restate the comparison between internal equivalence relations and
equivalence relations on `T`-points with `T` in a property, the transfer of points over a base,
apply the point description to kernel pairs, and guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AglibTest.ObjectPropertyEquivalenceRelation

variable {C : Type u} [Category.{v} C]

/-- An internal equivalence relation is tested on three universal points with `P`. -/
theorem isEquivalenceRelation_iff (P : ObjectProperty C) {R X : C} (p₁ p₂ : R ⟶ X)
    [JointlyMono₂ p₁ p₂] [HasPullback p₂ p₁] (hX : P X) (hR : P R)
    (hRR : P (pullback p₂ p₁)) :
    IsEquivalenceRelation p₁ p₂ ↔ ∀ T, P T → _root_.Equivalence (pointsRelation p₁ p₂ T) :=
  ObjectProperty.isEquivalenceRelation_iff_points P p₁ p₂ hX hR hRR

/-- The kernel pair of a morphism relates exactly the points with the same image, and it is an
equivalence relation on all points. -/
theorem equivalence_pointsRelation_kernelPair [HasPullbacks C] {X Y : C} (f : X ⟶ Y) (T : C) :
    _root_.Equivalence (pointsRelation (pullback.fst f f) (pullback.snd f f) T) :=
  (IsKernelPair.equivalenceRelation f _ _ (pullbackIsPullback (pullback.snd f f)
    (pullback.fst f f)) (IsPullback.of_hasPullback f f)).equivalence_pointsRelation T

/-- Points over a base are related exactly when their underlying morphisms are. -/
theorem over_pointsRelation_iff {S : C} {R X T : Over S} (p₁ p₂ : R ⟶ X) (a b : T ⟶ X) :
    pointsRelation p₁ p₂ T a b ↔ pointsRelation p₁.left p₂.left T.left a.left b.left :=
  Over.pointsRelation_iff a b

/-- Equivalence relations on points over a base are those on points of the underlying objects. -/
theorem over_equivalence_pointsRelation_iff {S : C} {R X : Over S} (p₁ p₂ : R ⟶ X)
    (P : ObjectProperty C) :
    (∀ T : Over S, P T.left → _root_.Equivalence (pointsRelation p₁ p₂ T)) ↔
      ∀ T : C, P T → _root_.Equivalence (pointsRelation p₁.left p₂.left T) :=
  Over.equivalence_pointsRelation_iff P

/-- info: 'AglibTest.ObjectPropertyEquivalenceRelation.isEquivalenceRelation_iff' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ObjectPropertyEquivalenceRelation.isEquivalenceRelation_iff

/-- info: 'AglibTest.ObjectPropertyEquivalenceRelation.equivalence_pointsRelation_kernelPair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ObjectPropertyEquivalenceRelation.equivalence_pointsRelation_kernelPair

/-- info: 'AglibTest.ObjectPropertyEquivalenceRelation.over_equivalence_pointsRelation_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ObjectPropertyEquivalenceRelation.over_equivalence_pointsRelation_iff

end AglibTest.ObjectPropertyEquivalenceRelation
