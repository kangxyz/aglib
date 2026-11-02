/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.NatTrans.CompositeExchangeToTarget
public import Aglib.CategoryTheory.NatTrans.ExchangeToTarget

/-! # Whole original exchange squares restrict through an actual object-property lift -/
@[expose] public noncomputable section
namespace CategoryTheory
variable {A B C A' B' C' : Type*}
  [Category* A] [Category* B] [Category* C]
  [Category* A'] [Category* B'] [Category* C']
  {J S : A ⥤ B} {R : B ⥤ C} {F : A ⥤ C}
  {J' S' : A' ⥤ B'} {R' : B' ⥤ C'} {F' : A' ⥤ C'}
  {G : C ⥤ C'} {H : B ⥤ B'} {G' : A ⥤ A'}

/-- The supplied iso is exactly the original restricted exchange with its original lift. -/
def RestrictedCompositeExchangeFormula
    (βR : R ⋙ G ⟶ H ⋙ R') (e : J ⋙ H ≅ G' ⋙ J')
    (P : ObjectProperty A) (P' : ObjectProperty A')
    (hG' : ∀ K : P.FullSubcategory, P' ((P.ι ⋙ G').obj K))
    (hβ : NatTrans.IsIsoOn P (compositeExchange βR e))
    (σ : (P.ι ⋙ (J ⋙ R)) ⋙ G ≅
      P'.lift (P.ι ⋙ G') hG' ⋙ (P'.ι ⋙ (J' ⋙ R'))) : Prop :=
  σ = Functor.associator _ _ _ ≪≫ (compositeExchange βR e).isoOn P hβ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl ((P'.lift (P.ι ⋙ G') hG') ⋙ P'.ι)).symm
      (J' ⋙ R') ≪≫ Functor.associator _ _ _

/-- Evaluate components only in abstract categories, retaining both whole original inputs. -/
theorem compositeExchange_toTarget_restrict
    (b : J ⟶ S) (b' : J' ⟶ S') (τ : S ⋙ R ≅ F) (τ' : S' ⋙ R' ≅ F')
    (βR : R ⋙ G ⟶ H ⋙ R') (e : J ⋙ H ≅ G' ⋙ J') (βF : F ⋙ G ⟶ G' ⋙ F')
    (P : ObjectProperty A) (P' : ObjectProperty A')
    (hG' : ∀ K : P.FullSubcategory, P' ((P.ι ⋙ G').obj K))
    (hβ : NatTrans.IsIsoOn P (compositeExchange βR e))
    (σ : (P.ι ⋙ (J ⋙ R)) ⋙ G ≅
      P'.lift (P.ι ⋙ G') hG' ⋙ (P'.ι ⋙ (J' ⋙ R')))
    (hσ : RestrictedCompositeExchangeFormula βR e P P' hG' hβ σ)
    (h : CompositeExchangeToTargetEquation b b' τ τ' βR e βF) :
    ExchangeToTargetEquation
      (Functor.whiskerLeft P.ι (Functor.whiskerRight b R ≫ τ.hom))
      (Functor.whiskerLeft P'.ι (Functor.whiskerRight b' R' ≫ τ'.hom))
      σ.hom (Functor.whiskerLeft P.ι βF) := by
  rw [hσ]
  apply NatTrans.ext
  funext K
  have hK := congrArg (fun z => z.app K.obj) h
  simp only [NatTrans.isoOn, asIso_hom, Iso.trans_hom, Iso.symm_hom,
    Iso.refl_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, NatTrans.id_app, Functor.map_id,
    Functor.comp_obj, ObjectProperty.ι_obj,
    Category.id_comp, Category.comp_id]
  exact (congrArg (fun z => z ≫ R'.map (b'.app (G'.obj K.obj)) ≫
    τ'.hom.app (G'.obj K.obj))
    (Category.comp_id ((compositeExchange βR e).app K.obj))).trans hK
end CategoryTheory
