/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Yoneda

/-!
# Restricting a representation to a full subcategory

Let `G : D ⥤ C` be fully faithful and `F : Cᵒᵖ ⥤ Type w`, with values in any universe. A
representation `e` of `F` by `G.obj Y` restricts to a representation of `G.op ⋙ F` by `Y`
(`Functor.FullyFaithful.representableBy`): for `T` in `D`,

`(T ⟶ Y) ≃ (G.obj T ⟶ G.obj Y) ≃ F(G.obj T)`,

the first bijection being `G` on morphisms. No hypothesis on `F` is needed: naturality in `T`
is the naturality of `e`.

For properties of objects `P ≤ Q` of `C`, this applies to the inclusion
`ObjectProperty.ιOfLE h : P.FullSubcategory ⥤ Q.FullSubcategory`
(`ObjectProperty.representableByιOfLE`): a presheaf on the objects satisfying `Q`, represented by
an object satisfying `P`, is represented by the same object on the objects satisfying `P`. The
consumer is the passage from locally Noetherian test schemes to test schemes locally of finite
type over a locally Noetherian base
(`Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyOfFiniteTypeOver`).
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open Opposite

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **Restriction of a representation along a fully faithful functor.** If `G : D ⥤ C` is fully
faithful and `F : Cᵒᵖ ⥤ Type w` is represented by `G.obj Y`, then `G.op ⋙ F` is represented by
`Y`, through `(T ⟶ Y) ≃ (G.obj T ⟶ G.obj Y)`. -/
def Functor.FullyFaithful.representableBy {G : D ⥤ C} (hG : G.FullyFaithful)
    {F : Cᵒᵖ ⥤ Type w} {Y : D} (e : F.RepresentableBy (G.obj Y)) :
    (G.op ⋙ F).RepresentableBy Y where
  homEquiv := hG.homEquiv.trans e.homEquiv
  homEquiv_comp f g := by
    change e.homEquiv (G.map (f ≫ g)) = F.map (G.map f).op (e.homEquiv (G.map g))
    rw [G.map_comp, e.homEquiv_comp]

theorem Functor.FullyFaithful.representableBy_homEquiv {G : D ⥤ C} (hG : G.FullyFaithful)
    {F : Cᵒᵖ ⥤ Type w} {Y : D} (e : F.RepresentableBy (G.obj Y)) {T : D} (f : T ⟶ Y) :
    (hG.representableBy e).homEquiv f = e.homEquiv (G.map f) :=
  rfl

namespace ObjectProperty

variable {P Q : ObjectProperty C}

/-- **Restriction of a representation to a smaller property of objects.** For `h : P ≤ Q`, a
presheaf `F` on the objects satisfying `Q`, represented by an object `Y` satisfying `P`, is
represented by `Y` on the objects satisfying `P`. -/
def representableByιOfLE (h : P ≤ Q) {F : Q.FullSubcategoryᵒᵖ ⥤ Type w} {Y : P.FullSubcategory}
    (e : F.RepresentableBy ((ιOfLE h).obj Y)) : ((ιOfLE h).op ⋙ F).RepresentableBy Y :=
  (fullyFaithfulιOfLE h).representableBy e

theorem representableByιOfLE_homEquiv (h : P ≤ Q) {F : Q.FullSubcategoryᵒᵖ ⥤ Type w}
    {Y : P.FullSubcategory} (e : F.RepresentableBy ((ιOfLE h).obj Y)) {T : P.FullSubcategory}
    (f : T ⟶ Y) :
    (representableByιOfLE h e).homEquiv f = e.homEquiv (homMk f.hom) :=
  rfl

end ObjectProperty

end CategoryTheory
