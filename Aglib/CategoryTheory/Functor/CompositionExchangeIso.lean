/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionExchangeTransport

/-! # The original composition exchange with all associators displayed -/

@[expose] public section
namespace CategoryTheory

variable {A B C A' B' C' : Type*}
  [Category* A] [Category* B] [Category* C]
  [Category* A'] [Category* B'] [Category* C']
  {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
  {F' : A' ⥤ B'} {G' : B' ⥤ C'} {H' : A' ⥤ C'}
  {U : A ⥤ A'} {V : B ⥤ B'} {W : C ⥤ C'}

/-- The component law is the original isomorphism pasting, with actual associators. -/
theorem compositionExchangeIso
    (κ : F ⋙ G ≅ H) (κ' : F' ⋙ G' ≅ H')
    (βF : F ⋙ V ≅ U ⋙ F') (βG : G ⋙ W ≅ V ⋙ G')
    (βH : H ⋙ W ≅ U ⋙ H')
    (h : CompositionExchangeEquation κ κ' βF.hom βG.hom βH.hom) :
    Functor.isoWhiskerRight κ W ≪≫ βH =
      Functor.associator F G W ≪≫ Functor.isoWhiskerLeft F βG ≪≫
        (Functor.associator F V G').symm ≪≫ Functor.isoWhiskerRight βF G' ≪≫
          Functor.associator U F' G' ≪≫ Functor.isoWhiskerLeft U κ' := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using h X

end CategoryTheory
