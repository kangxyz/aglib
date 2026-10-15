/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Pushout squares lifted through a full subcategory

An actual pushout square of mapped arrows remains a pushout after lifting the
functor through a full subcategory. The membership witness and all four mapped
arrows are retained. No preservation assumption on the source inclusion and no
existence of arbitrary pushouts in the full subcategory are required.

Source: `Quillen/CategoryTheory/Limits/FullSubcategoryLiftPushout.lean`
from the supplied Quillen archive.
Source SHA-256: `3b83a08211e6ee40df163b7cd1373f8cd9c9de2cf709d0875268f9832b56328d`.
All declarations are migrated with their original hypotheses and maps.
-/
@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty

open CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Reflect an actual mapped pushout square through the full target inclusion. -/
theorem isPushout_lift (P : ObjectProperty D) (F : C ⥤ D)
    (hF : ∀ X, P (F.obj X)) {A B E T : C}
    {f : A ⟶ B} {g : A ⟶ E} {i : B ⟶ T} {j : E ⟶ T}
    (h : IsPushout (F.map f) (F.map g) (F.map i) (F.map j)) :
    IsPushout ((P.lift F hF).map f) ((P.lift F hF).map g)
      ((P.lift F hF).map i) ((P.lift F hF).map j) := by
  apply IsPushout.of_map_of_faithful P.ι
  exact h

end CategoryTheory.ObjectProperty
