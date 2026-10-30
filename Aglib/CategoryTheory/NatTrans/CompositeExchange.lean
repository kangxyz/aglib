/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.IsIsoOn
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Pasting two original exchange transformations

The abstract pasting retains the specified right exchange and left comparison.
Its exact component formula and object-property invertibility are shared by
concrete consumers without expanding their category carriers. Native restriction
to a full subcategory retains the unchanged transformation.
-/

@[expose] public noncomputable section

universe uA vA uB vB uC vC uA' vA' uB' vB' uC' vC'

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {C : Type uC} {A' : Type uA'} {B' : Type uB'} {C' : Type uC'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vA'} A'] [Category.{vB'} B'] [Category.{vC'} C']
  {J : A ⥤ B} {R : B ⥤ C} {G : C ⥤ C'}
  {H : B ⥤ B'} {R' : B' ⥤ C'} {G' : A ⥤ A'} {J' : A' ⥤ B'}

/-- Paste a right exchange with a left comparison, retaining the original maps. -/
def compositeExchange (β : R ⋙ G ⟶ H ⋙ R') (e : J ⋙ H ≅ G' ⋙ J') :
    (J ⋙ R) ⋙ G ⟶ G' ⋙ (J' ⋙ R') :=
  (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft J β ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e.hom R' ≫
    (Functor.associator _ _ _).hom

/-- The pasted comparison has the literal original component formula. -/
theorem compositeExchange_app (β : R ⋙ G ⟶ H ⋙ R') (e : J ⋙ H ≅ G' ⋙ J') (K : A) :
    (compositeExchange β e).app K = β.app (J.obj K) ≫ R'.map (e.hom.app K) := by
  simp only [compositeExchange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

/-- Pasting preserves invertibility on a specified property, retained as one predicate. -/
theorem compositeExchange_isIsoOn (β : R ⋙ G ⟶ H ⋙ R')
    (e : J ⋙ H ≅ G' ⋙ J') (P : ObjectProperty A)
    (hβ : NatTrans.IsIsoOn P (Functor.whiskerLeft J β)) :
    NatTrans.IsIsoOn P (compositeExchange β e) := by
  intro K hK
  let : IsIso (β.app (J.obj K)) := hβ K hK
  rw [compositeExchange_app]
  infer_instance

end CategoryTheory
