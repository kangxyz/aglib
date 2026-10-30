/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.SpecLocalRing

/-!
# Consumer checks for spectra of local rings and actual scheme stalks

The structural scalar triangle needs only a commutative base ring. Existence
and injectivity of the local stalk factorization need only the displayed local
ring and local-map hypotheses. This test imports the lower stalk leaf directly.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AglibTest.StalkSpecLocalRing

example {R : Type u} [CommRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) (x : X) :
    X.fromSpecStalk x ≫ π = Spec.map (CommRingCat.ofHom (π.stalkScalar x)) :=
  fromSpecStalk_comp_eq_spec_map_stalkScalar π x

example {X : Scheme.{u}} {x : X} {R : CommRingCat.{u}} [IsLocalRing R]
    {φ φ' : X.presheaf.stalk x ⟶ R} [IsLocalHom φ.hom] [IsLocalHom φ'.hom]
    (h : Spec.map φ ≫ X.fromSpecStalk x = Spec.map φ' ≫ X.fromSpecStalk x) : φ = φ' :=
  spec_map_comp_fromSpecStalk_injective h

example {X : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]
    (g : Spec R ⟶ X) {x : X} (hx : g (closedPoint R) = x) :
    ∃ φ : X.presheaf.stalk x ⟶ R, IsLocalHom φ.hom ∧
      Spec.map φ ≫ X.fromSpecStalk x = g :=
  exists_spec_map_comp_fromSpecStalk g hx

end AglibTest.StalkSpecLocalRing

/--
info: 'AlgebraicGeometry.Scheme.fromSpecStalk_comp_eq_spec_map_stalkScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.fromSpecStalk_comp_eq_spec_map_stalkScalar

/--
info: 'AlgebraicGeometry.Scheme.spec_map_comp_fromSpecStalk_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.spec_map_comp_fromSpecStalk_injective

/--
info: 'AlgebraicGeometry.Scheme.exists_spec_map_comp_fromSpecStalk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.exists_spec_map_comp_fromSpecStalk
