/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ObjectProperty.Yoneda

/-!
# Yoneda tests on the objects of a property

The declarations below restate the isomorphism and monomorphism tests on the objects of a
property, recover Mathlib's Yoneda test for the trivial property, and guard their axioms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AglibTest.ObjectPropertyYoneda

variable {C : Type u} [Category.{v} C]

/-- Isomorphisms are detected by bijectivity on the points of a property. -/
theorem isIso_of_bijective (P : ObjectProperty C) {X Y : C} (hX : P X) (hY : P Y) (f : X ⟶ Y)
    (hf : ∀ T, P T → Function.Bijective fun x : T ⟶ X => x ≫ f) : IsIso f :=
  ObjectProperty.isIso_of_yoneda_map_bijective P hX hY f hf

/-- Monomorphisms are detected by injectivity on the points of a property containing the
diagonal object, and the diagonal is then an isomorphism. -/
theorem mono_of_injective (P : ObjectProperty C) {X Y : C} (f : X ⟶ Y) [HasPullback f f]
    (hXX : P (pullback f f)) (hf : ∀ T, P T → Function.Injective fun x : T ⟶ X => x ≫ f) :
    Mono f ∧ IsIso (pullback.diagonal f) ∧ pullback.fst f f = pullback.snd f f :=
  ⟨ObjectProperty.mono_of_yoneda_map_injective f hXX hf,
    ObjectProperty.isIso_diagonal_of_yoneda_map_injective f hXX hf,
    ObjectProperty.fst_eq_snd_of_yoneda_map_injective f hXX hf⟩

/-- With the trivial property, Mathlib's Yoneda test for isomorphisms is recovered. -/
example {X Y : C} (f : X ⟶ Y) (hf : ∀ T, Function.Bijective fun x : T ⟶ X => x ≫ f) :
    IsIso f :=
  ObjectProperty.isIso_of_yoneda_map_bijective (fun _ => True) trivial trivial f fun T _ => hf T

/-- info: 'AglibTest.ObjectPropertyYoneda.isIso_of_bijective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ObjectPropertyYoneda.isIso_of_bijective

/-- info: 'AglibTest.ObjectPropertyYoneda.mono_of_injective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ObjectPropertyYoneda.mono_of_injective

end AglibTest.ObjectPropertyYoneda
