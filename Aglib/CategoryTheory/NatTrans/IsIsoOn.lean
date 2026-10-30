/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering

/-! # Invertibility on an object property and the original restriction -/

@[expose] public noncomputable section

universe uB vB uC vC uD vD uE vE

namespace CategoryTheory

/-- Invertibility of the original components on a specified property of objects. -/
def NatTrans.IsIsoOn {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
    {F G : B ⥤ C} (P : ObjectProperty B) (τ : F ⟶ G) : Prop :=
  ∀ K, P K → IsIso (τ.app K)

/-- Restriction of an original transformation invertible on a property is a native NatIso. -/
def NatTrans.isoOn {D : Type uD} {E : Type uE} [Category.{vD} D] [Category.{vE} E]
    {F G : D ⥤ E} (α : F ⟶ G) (P : ObjectProperty D) (hα : NatTrans.IsIsoOn P α) :
    P.ι ⋙ F ≅ P.ι ⋙ G := by
  let β := Functor.whiskerLeft P.ι α
  have (K : P.FullSubcategory) : IsIso (β.app K) := hα K.obj K.property
  let : IsIso β := NatIso.isIso_of_isIso_app β
  exact asIso β

/-- Restriction changes no original component map. -/
theorem NatTrans.isoOn_hom_app {D : Type uD} {E : Type uE} [Category.{vD} D] [Category.{vE} E]
    {F G : D ⥤ E} (α : F ⟶ G) (P : ObjectProperty D) (hα : NatTrans.IsIsoOn P α)
    (K : P.FullSubcategory) : (α.isoOn P hα).hom.app K = α.app K.obj := rfl

end CategoryTheory
