/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CompositeExchange

/-! # Exchange restricted through a full-subcategory lift -/

@[expose] public noncomputable section
namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  (P : ObjectProperty A) (Q : ObjectProperty B)
  (H : A ⥤ B) (R : A ⥤ C) (S : B ⥤ D) (G : C ⥤ D)
  (h : ∀ K : P.FullSubcategory, Q ((P.ι ⋙ H).obj K))

/-- A full-subcategory lift changes no component of the original exchange. -/
theorem compositeExchange_lift_app (β : R ⋙ G ⟶ H ⋙ S) (K : P.FullSubcategory) :
    (compositeExchange (G' := Q.lift (P.ι ⋙ H) h) (J' := Q.ι)
      β (Iso.refl _)).app K = β.app K.obj := by
  rw [compositeExchange_app]
  change β.app K.obj ≫ S.map (𝟙 _) = β.app K.obj
  rw [S.map_id]
  exact Category.comp_id (β.app K.obj)

end CategoryTheory
