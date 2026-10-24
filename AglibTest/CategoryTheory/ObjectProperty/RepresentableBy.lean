/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ObjectProperty.RepresentableBy

/-! Focused consumer of the restriction of a representation along a fully faithful functor and
to a smaller property of objects, with axiom guards. -/

@[expose] public section

open CategoryTheory Opposite

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

/-- Restriction along a fully faithful functor is `e` composed with the functor on morphisms. -/
example {D : Type u₂} [Category.{v₂} D] {G : D ⥤ C} (hG : G.FullyFaithful)
    {F : Cᵒᵖ ⥤ Type w} {Y : D} (e : F.RepresentableBy (G.obj Y)) {T : D} (f : T ⟶ Y) :
    (hG.representableBy e).homEquiv f = e.homEquiv (G.map f) :=
  Functor.FullyFaithful.representableBy_homEquiv hG e f

/-- A representation on the objects of `Q` by an object of `P ≤ Q` restricts to the objects of
`P`. -/
example {P Q : ObjectProperty C} (h : P ≤ Q) {F : Q.FullSubcategoryᵒᵖ ⥤ Type w}
    {Y : P.FullSubcategory} (e : F.RepresentableBy ((ObjectProperty.ιOfLE h).obj Y))
    {T : P.FullSubcategory} (f : T ⟶ Y) :
    ((ObjectProperty.ιOfLE h).op ⋙ F).IsRepresentable ∧
      (ObjectProperty.representableByιOfLE h e).homEquiv f =
        e.homEquiv (ObjectProperty.homMk f.hom) :=
  ⟨(ObjectProperty.representableByιOfLE h e).isRepresentable,
    ObjectProperty.representableByιOfLE_homEquiv h e f⟩

/-- A representation on all of `C` by an object satisfying `P` restricts to the full subcategory
of `P`. -/
example {P : ObjectProperty C} {F : Cᵒᵖ ⥤ Type w} {Y : P.FullSubcategory}
    (e : F.RepresentableBy Y.obj) {T : P.FullSubcategory} (f : T ⟶ Y) :
    (P.fullyFaithfulι.representableBy e).homEquiv f = e.homEquiv f.hom :=
  Functor.FullyFaithful.representableBy_homEquiv P.fullyFaithfulι (Y := Y) e f

/--
info: 'CategoryTheory.Functor.FullyFaithful.representableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.FullyFaithful.representableBy

/--
info: 'CategoryTheory.ObjectProperty.representableByιOfLE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.ObjectProperty.representableByιOfLE
