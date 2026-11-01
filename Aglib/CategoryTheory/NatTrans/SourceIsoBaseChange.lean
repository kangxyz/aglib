/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.RefinedSourcePasting
public import Aglib.CategoryTheory.NatTrans.SourceExchange.Pasting
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA' uD uD' uE uE' vA vA' vD vD' vE vE'

/-- Whole original source-isomorphism/base-change comparison square. -/
def SourceIsoBaseChangeEquation
    {A : Type uA} {A' : Type uA'} {D : Type uD} {D' : Type uD'} {E : Type uE} {E' : Type uE'}
    [Category.{vA} A] [Category.{vA'} A'] [Category.{vD} D] [Category.{vD'} D']
    [Category.{vE} E] [Category.{vE'} E']
    {F : A ⥤ E} {F' : A' ⥤ E} {G : D ⥤ E'} {G' : D' ⥤ E'} {B : E ⥤ E'}
    {V : A ⥤ A'} {W : A ⥤ D} {W' : A' ⥤ D'} {V' : D ⥤ D'}
    (s : F ≅ V ⋙ F') (β' : F' ⋙ B ⟶ W' ⋙ G') (β : F ⋙ B ⟶ W ⋙ G)
    (s' : G ≅ V' ⋙ G') (c : V ⋙ W' ≅ W ⋙ V') : Prop :=
  ∀ K, B.map (s.hom.app K) ≫ β'.app (V.obj K) ≫ G'.map (c.hom.app K) =
    β.app K ≫ s'.hom.app (W.obj K)

/-- The two proved routes through the same original composite exchange give
interchange, with the original target refinement absorbed by its actual formula. -/
theorem sourceIsoBaseChange_of_before_after
    {A : Type uA} {A' : Type uA'} {D : Type uD} {D' : Type uD'} {E : Type uE} {E' : Type uE'}
    [Category.{vA} A] [Category.{vA'} A'] [Category.{vD} D] [Category.{vD'} D']
    [Category.{vE} E] [Category.{vE'} E']
    {F : A ⥤ E} {F' : A' ⥤ E} {G : D ⥤ E'} {G' R : D' ⥤ E'} {B : E ⥤ E'}
    {V : A ⥤ A'} {W : A ⥤ D} {W' : A' ⥤ D'} {V' : D ⥤ D'} {H : A ⥤ D'}
    (s : F ≅ V ⋙ F') (β' : F' ⋙ B ⟶ W' ⋙ G') (β : F ⋙ B ⟶ W ⋙ G)
    (sR : G ≅ V' ⋙ R) (t : R ⟶ G') (s' : G ≅ V' ⋙ G')
    (βc : F ⋙ B ⟶ H ⋙ G') (c₁ : H ≅ V ⋙ W') (c₂ : H ≅ W ⋙ V')
    (hb : SourceIsoBeforeExchangeEquation s β' βc c₁)
    (ha : RefinedSourceIsoPastingEquation β βc c₂ sR t)
    (hs : s'.hom = sR.hom ≫ Functor.whiskerLeft V' t) :
    SourceIsoBaseChangeEquation s β' β s' (c₁.symm ≪≫ c₂) := by
  intro K
  have hc : G'.map (c₁.hom.app K) ≫ G'.map ((c₁.symm ≪≫ c₂).hom.app K) =
      G'.map (c₂.hom.app K) := by
    rw [← G'.map_comp]
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Iso.hom_inv_id_app_assoc]
  calc
    _ = (βc.app K ≫ G'.map (c₁.hom.app K)) ≫
        G'.map ((c₁.symm ≪≫ c₂).hom.app K) := by rw [← Category.assoc, hb K]
    _ = βc.app K ≫ G'.map (c₂.hom.app K) := by rw [Category.assoc, hc]
    _ = _ := by
      simpa only [hs, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
        Functor.comp_obj] using ha K

end CategoryTheory
