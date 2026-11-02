/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.CategoryTheory.NatTrans.CartesianSourceExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoMapPasting

/-! # Source pasting computes the original transported exchange -/

@[expose] public section
namespace CategoryTheory
open AlgebraicGeometry.Scheme.EtaleCohomology

variable {A B C D E : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
  {F : A ⥤ D} {P : D ⥤ E} {V : A ⥤ B} {W : B ⥤ C} {U U' : A ⥤ C}
  {R : B ⥤ E} {Q : C ⥤ E}

/-- Retain both the original source pasting and the actual source-arrow equality. -/
theorem cartesianExchangePasting
    (β : F ⋙ P ≅ V ⋙ R) (ψ : R ≅ W ⋙ Q) (c : U' ≅ V ⋙ W) (d : U ≅ U')
    (β' : F ⋙ P ⟶ U' ⋙ Q) (β₀ : F ⋙ P ⟶ U ⋙ Q)
    (hp : CompactifiedSourceIsoPastingEquation β.hom β' c ψ)
    (hd : β₀ ≫ Functor.whiskerRight d.hom Q = β') :
    (cartesianSourceExchange β ψ (d ≪≫ c)).hom = β₀ := by
  apply NatTrans.ext
  funext K
  have hdK := congrArg (fun z => z.app K) hd
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hdK
  rw [cartesianSourceExchange_hom_app, ← Category.assoc, ← hp K, ← hdK]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  simp only [← Q.map_comp, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
    Functor.map_id]
  exact Category.comp_id (β₀.app K)

end CategoryTheory
