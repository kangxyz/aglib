/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.EquivalenceRelation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Equivalence relations on locally Noetherian points

The declarations below restate the locally Noetherian test of schematic equivalence relations in
the setting of Nitsure's Theorem 6.8 (a closed subscheme `R` of `Z ×_S Z` with proper
projections), without monicity (injectivity on locally Noetherian points), and for relations given
on points over the base, and guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AglibTest.LocallyNoetherianEquivalenceRelation

/-- **A closed relation with proper projections** on a locally Noetherian scheme is an internal
equivalence relation exactly when it is one on locally Noetherian points. -/
theorem iff_of_isClosedImmersion {S R Z : Scheme.{u}} (π : Z ⟶ S)
    (j : R ⟶ pullback π π) [IsClosedImmersion j] [IsLocallyNoetherian Z]
    [IsProper (j ≫ pullback.fst π π)] :
    IsEquivalenceRelation (j ≫ pullback.fst π π) (j ≫ pullback.snd π π) ↔
      ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
        _root_.Equivalence (pointsRelation (j ≫ pullback.fst π π) (j ≫ pullback.snd π π) T) :=
  Scheme.isEquivalenceRelation_iff_locallyNoetherian_points_of_mono π j

/-- Without monicity: over a locally Noetherian base, a relation of finite type that is injective
with image an equivalence relation on locally Noetherian points is an internal equivalence
relation. -/
theorem isEquivalenceRelation_of_points {S R Z : Scheme.{u}} (π : Z ⟶ S) (p₁ p₂ : R ⟶ Z)
    (hp : p₁ ≫ π = p₂ ≫ π) [IsLocallyNoetherian S] [LocallyOfFiniteType π]
    [LocallyOfFiniteType p₁]
    (hinj : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (r r' : T ⟶ R),
      r ≫ p₁ = r' ≫ p₁ → r ≫ p₂ = r' ≫ p₂ → r = r')
    (h : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation p₁ p₂ T)) :
    IsEquivalenceRelation p₁ p₂ :=
  Scheme.isEquivalenceRelation_of_locallyNoetherian_points p₁ p₂ π hp hinj h

/-- Equivalence relations on locally Noetherian points over a base are those on locally Noetherian
points of the underlying schemes. -/
theorem equivalence_pointsRelation_over_iff {S : Scheme.{u}} {R Z : Over S} (p₁ p₂ : R ⟶ Z) :
    (∀ T : Scheme.LocallyNoetherianOver S, _root_.Equivalence (pointsRelation p₁ p₂ T.obj)) ↔
      ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
        _root_.Equivalence (pointsRelation p₁.left p₂.left T) :=
  Scheme.LocallyNoetherianOver.equivalence_pointsRelation_iff p₁ p₂

/-- **The internal version over a base**: for `p₁, p₂` over `S` whose underlying morphisms are
jointly monic, with `X`, `R` and `R ×_X R` locally Noetherian, `p₁, p₂` is an equivalence relation
in `Over S` exactly when it is one on locally Noetherian points over `S`. -/
theorem isEquivalenceRelation_over_iff {S : Scheme.{u}} {R Z : Over S} (p₁ p₂ : R ⟶ Z)
    [JointlyMono₂ p₁.left p₂.left] [IsLocallyNoetherian Z.left] [IsLocallyNoetherian R.left]
    [IsLocallyNoetherian (pullback p₂.left p₁.left)] :
    IsEquivalenceRelation p₁ p₂ ↔
      ∀ T : Scheme.LocallyNoetherianOver S, _root_.Equivalence (pointsRelation p₁ p₂ T.obj) :=
  have := Over.jointlyMono₂_of_left (p₁ := p₁) (p₂ := p₂)
  Scheme.LocallyNoetherianOver.isEquivalenceRelation_iff p₁ p₂

/-- info: 'AglibTest.LocallyNoetherianEquivalenceRelation.iff_of_isClosedImmersion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianEquivalenceRelation.iff_of_isClosedImmersion

/-- info: 'AglibTest.LocallyNoetherianEquivalenceRelation.isEquivalenceRelation_of_points'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianEquivalenceRelation.isEquivalenceRelation_of_points

/-- info: 'AglibTest.LocallyNoetherianEquivalenceRelation.equivalence_pointsRelation_over_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianEquivalenceRelation.equivalence_pointsRelation_over_iff

/-- info: 'AglibTest.LocallyNoetherianEquivalenceRelation.isEquivalenceRelation_over_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianEquivalenceRelation.isEquivalenceRelation_over_iff

end AglibTest.LocallyNoetherianEquivalenceRelation
