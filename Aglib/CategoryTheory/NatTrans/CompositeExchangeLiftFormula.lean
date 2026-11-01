/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CompositeExchangeLift

/-! # Whole original formula for full-subcategory exchange restriction -/

@[expose] public noncomputable section
namespace CategoryTheory
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  (P : ObjectProperty A) (Q : ObjectProperty B)
  (H : A ⥤ B) (R : A ⥤ C) (S : B ⥤ D) (G : C ⥤ D)
  (h : ∀ K : P.FullSubcategory, Q ((P.ι ⋙ H).obj K))

/-- Keep the complete restriction formula behind a regular predicate boundary. -/
def CompositeExchangeLiftFormula (β : R ⋙ G ⟶ H ⋙ S)
    (γ : (P.ι ⋙ R) ⋙ G ⟶ Q.lift (P.ι ⋙ H) h ⋙ (Q.ι ⋙ S)) : Prop :=
  ∀ K, γ.app K = β.app K.obj

/-- The original pasted comparison has this formula for every source object. -/
theorem compositeExchange_lift_formula (β : R ⋙ G ⟶ H ⋙ S) :
    CompositeExchangeLiftFormula P Q H R S G h β
      (compositeExchange (G' := Q.lift (P.ι ⋙ H) h) (J' := Q.ι) β (Iso.refl _)) :=
  compositeExchange_lift_app P Q H R S G h β

end CategoryTheory
