/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion

/-!
# Consumer checks for closed embeddings into projective spaces Zariski locally over the base

For `E : ProjectiveSpace.ZariskiLocalClosedImmersion f` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 4.8, p. 27, "projective Zariski locally over `S`"): the open cover of
the base, Noetherian coordinate rings over a locally Noetherian base, flatness, geometric
integrality and properness of the embedded families, properness of `f`, the equivalence with the
property `IsZariskiLocallyHProjective f`, and the affine case of a single closed subscheme of
`P(ι)_A` (`ofClosedImmersion`); axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

namespace AglibTest.ZariskiLocalClosedImmersion

variable {S X : Scheme.{u}} {f : X ⟶ S} (E : ZariskiLocalClosedImmersion f)

/-- The open cover of the base has the charts `j a`. -/
example (a : E.I) : E.openCover.f a = E.j a := rfl

/-- Over a locally Noetherian base the coordinate rings are Noetherian. -/
example [IsLocallyNoetherian S] (a : E.I) : IsNoetherianRing (E.A a) := inferInstance

/-- The embedded families inherit flatness and geometric integrality, and are proper. -/
example [Flat f] [GeometricallyIntegral f] (a : E.I) :
    Flat (E.c a ≫ toSpec (E.A a) (E.ι a)) ∧ GeometricallyIntegral (E.c a ≫ toSpec (E.A a) (E.ι a)) ∧
      IsProper (E.c a ≫ toSpec (E.A a) (E.ι a)) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- `f` is proper. -/
example : IsProper f := E.isProper

/-- **The affine case**: a closed subscheme `i : X ⟶ P(ι)_A` with `ι ≃ Fin (N + 1)` is projective
Zariski locally over `Spec A`, with the single chart `𝟙 (Spec A)` and the embedding
`X ×_{Spec A} Spec A ⟶ X ⟶ P(ι)_A`. -/
def ofClosedImmersion {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] {N : ℕ} (e : ι ≃ Fin (N + 1)) :
    ZariskiLocalClosedImmersion (i ≫ toSpec A ι) where
  I := PUnit
  A _ := A
  j _ := 𝟙 _
  covers x := ⟨PUnit.unit, by simp⟩
  ι _ := ι
  N _ := N
  e _ := e
  c _ := pullback.fst _ _ ≫ i
  c_comp_toSpec _ := by rw [Category.assoc, pullback.condition, Category.comp_id]

/-- In the affine case the properness of `ZariskiLocalClosedImmersion.isProper` is that of a closed
subscheme of `P(ι)_A`. -/
example {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι)
    [IsClosedImmersion i] {N : ℕ} (e : ι ≃ Fin (N + 1)) : IsProper (i ≫ toSpec A ι) :=
  (ofClosedImmersion i e).isProper

/-- Embeddings give the property `IsZariskiLocallyHProjective`, and the property gives
embeddings. -/
example : IsZariskiLocallyHProjective f := E.isZariskiLocallyHProjective

example [IsZariskiLocallyHProjective f] : Nonempty (ZariskiLocalClosedImmersion f) :=
  ZariskiLocalClosedImmersion.nonempty_of_isZariskiLocallyHProjective f

/-- A closed subscheme of `P(ι)_A` is H-projective Zariski locally over `Spec A`. -/
example {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι)
    [IsClosedImmersion i] {N : ℕ} (e : ι ≃ Fin (N + 1)) :
    IsZariskiLocallyHProjective (i ≫ toSpec A ι) :=
  (ofClosedImmersion i e).isZariskiLocallyHProjective

end AglibTest.ZariskiLocalClosedImmersion

/-- info: 'AlgebraicGeometry.IsZariskiLocallyHProjective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.IsZariskiLocallyHProjective

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.isZariskiLocallyHProjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.isZariskiLocallyHProjective

/-- info:
'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.nonempty_of_isZariskiLocallyHProjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.nonempty_of_isZariskiLocallyHProjective

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.openCover' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.openCover

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.isNoetherianRing' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.isNoetherianRing

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.flat_c_comp_toSpec' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.flat_c_comp_toSpec

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.geometricallyIntegral_c_comp_toSpec'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.geometricallyIntegral_c_comp_toSpec

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.isProper_c_comp_toSpec' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.isProper_c_comp_toSpec

/-- info: 'AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.isProper' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion.isProper

/-- info: 'AglibTest.ZariskiLocalClosedImmersion.ofClosedImmersion' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ZariskiLocalClosedImmersion.ofClosedImmersion
