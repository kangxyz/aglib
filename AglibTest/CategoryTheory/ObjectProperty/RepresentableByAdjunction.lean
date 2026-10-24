/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ObjectProperty.RepresentableByAdjunction

/-! Focused consumer of the transport of a representation along an adjunction, on full
subcategories, with axiom guards. -/

@[expose] public section

open CategoryTheory Opposite

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C}

/-- `T ↦ F(L T)` is represented by `R Y`, and the bijection is the inverse adjunction bijection
followed by the given representation. -/
example (adj : L ⊣ R) {P : ObjectProperty C} {Q : ObjectProperty D}
    (hL : ∀ T : P.FullSubcategory, Q (L.obj T.obj)) {F : Q.FullSubcategoryᵒᵖ ⥤ Type w}
    {Y : Q.FullSubcategory} (e : F.RepresentableBy Y) (hY : P (R.obj Y.obj))
    {T : P.FullSubcategory} (f : T ⟶ ⟨R.obj Y.obj, hY⟩) :
    ((Q.lift (P.ι ⋙ L) hL).op ⋙ F).IsRepresentable ∧
      (ObjectProperty.representableByLiftOfAdjunction adj hL e hY).homEquiv f =
        e.homEquiv (ObjectProperty.homMk ((adj.homEquiv T.obj Y.obj).symm f.hom) :
          (Q.lift (P.ι ⋙ L) hL).obj T ⟶ Y) :=
  ⟨(ObjectProperty.representableByLiftOfAdjunction adj hL e hY).isRepresentable,
    ObjectProperty.representableByLiftOfAdjunction_homEquiv adj hL e hY f⟩

/-- Naturality in the test object: precomposition corresponds to the restriction maps of
`T ↦ F(L T)`. -/
example (adj : L ⊣ R) {P : ObjectProperty C} {Q : ObjectProperty D}
    (hL : ∀ T : P.FullSubcategory, Q (L.obj T.obj)) {F : Q.FullSubcategoryᵒᵖ ⥤ Type w}
    {Y : Q.FullSubcategory} (e : F.RepresentableBy Y) (hY : P (R.obj Y.obj))
    {T T' : P.FullSubcategory} (f : T ⟶ T') (x : T' ⟶ ⟨R.obj Y.obj, hY⟩) :
    (ObjectProperty.representableByLiftOfAdjunction adj hL e hY).homEquiv (f ≫ x) =
      F.map ((Q.lift (P.ι ⋙ L) hL).map f).op
        ((ObjectProperty.representableByLiftOfAdjunction adj hL e hY).homEquiv x) :=
  (ObjectProperty.representableByLiftOfAdjunction adj hL e hY).homEquiv_comp f x

/--
info: 'CategoryTheory.ObjectProperty.representableByLiftOfAdjunction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.ObjectProperty.representableByLiftOfAdjunction
