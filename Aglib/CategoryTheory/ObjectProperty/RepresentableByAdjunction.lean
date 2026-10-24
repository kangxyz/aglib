/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Yoneda

/-!
# Transporting a representation along an adjunction, on full subcategories

Let `adj : L ⊣ R` be an adjunction with `L : C ⥤ D`, and let `P` and `Q` be properties of objects
of `C` and `D` such that `L` sends objects satisfying `P` to objects satisfying `Q` (`hL`). Write
`Q.lift (P.ι ⋙ L) hL : P.FullSubcategory ⥤ Q.FullSubcategory` for the functor induced by `L`. If a
presheaf `F : Q.FullSubcategoryᵒᵖ ⥤ Type w` is represented by `Y` and `R.obj Y.obj` satisfies
`P`, then `(Q.lift (P.ι ⋙ L) hL).op ⋙ F` is represented by `R.obj Y.obj`
(`ObjectProperty.representableByLiftOfAdjunction`): for `T` satisfying `P`,

`(T ⟶ R Y) ≃ (L T ⟶ Y) ≃ F(L T)`,

the first bijection being the inverse of the adjunction bijection and the second the given
representation. The adjunction need not restrict to the full subcategories; only `R.obj Y.obj` is
required to satisfy `P`. Naturality in `T` is the naturality of the adjunction bijection
(`Adjunction.homEquiv_naturality_left_symm`) and of the given representation.

The consumer is the base change of a scheme representing a functor on locally Noetherian test
schemes, with `L = Over.map g` and `R = Over.pullback g`
(`Aglib.AlgebraicGeometry.Picard.BaseChangeRepresentableBy`).
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open Opposite

namespace CategoryTheory.ObjectProperty

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {L : C ⥤ D} {R : D ⥤ C}

/-- **Transport of a representation along an adjunction, on full subcategories.** For
`adj : L ⊣ R`, properties of objects `P` of `C` and `Q` of `D` with `L` sending `P` into `Q`, and a
presheaf `F` on the objects satisfying `Q` represented by `Y`, the presheaf `T ↦ F(L T)` on the
objects satisfying `P` is represented by `R.obj Y.obj`, provided that this object satisfies `P`. -/
def representableByLiftOfAdjunction (adj : L ⊣ R) {P : ObjectProperty C} {Q : ObjectProperty D}
    (hL : ∀ T : P.FullSubcategory, Q (L.obj T.obj)) {F : Q.FullSubcategoryᵒᵖ ⥤ Type w}
    {Y : Q.FullSubcategory} (e : F.RepresentableBy Y) (hY : P (R.obj Y.obj)) :
    ((Q.lift (P.ι ⋙ L) hL).op ⋙ F).RepresentableBy (⟨R.obj Y.obj, hY⟩ : P.FullSubcategory) where
  homEquiv {T} := P.fullyFaithfulι.homEquiv.trans
    ((adj.homEquiv T.obj Y.obj).symm.trans
      ((Q.fullyFaithfulι.homEquiv (X := (Q.lift (P.ι ⋙ L) hL).obj T) (Y := Y)).symm.trans
        e.homEquiv))
  homEquiv_comp {T T'} f x :=
    (congrArg (fun z => e.homEquiv (homMk z : (Q.lift (P.ι ⋙ L) hL).obj T ⟶ Y))
      (adj.homEquiv_naturality_left_symm f.hom x.hom)).trans
      (e.homEquiv_comp ((Q.lift (P.ι ⋙ L) hL).map f)
        (homMk ((adj.homEquiv T'.obj Y.obj).symm x.hom) : (Q.lift (P.ι ⋙ L) hL).obj T' ⟶ Y))

theorem representableByLiftOfAdjunction_homEquiv (adj : L ⊣ R) {P : ObjectProperty C}
    {Q : ObjectProperty D} (hL : ∀ T : P.FullSubcategory, Q (L.obj T.obj))
    {F : Q.FullSubcategoryᵒᵖ ⥤ Type w} {Y : Q.FullSubcategory} (e : F.RepresentableBy Y)
    (hY : P (R.obj Y.obj)) {T : P.FullSubcategory} (f : T ⟶ ⟨R.obj Y.obj, hY⟩) :
    (representableByLiftOfAdjunction adj hL e hY).homEquiv f =
      e.homEquiv
        (homMk ((adj.homEquiv T.obj Y.obj).symm f.hom) : (Q.lift (P.ι ⋙ L) hL).obj T ⟶ Y) :=
  rfl

end CategoryTheory.ObjectProperty
