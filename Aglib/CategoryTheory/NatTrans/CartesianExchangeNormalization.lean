/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.CategoryTheory.NatTrans.CartesianSourceExchange

/-! # Normalizing an exchange and an actual source comparison

Original naturality moves the normalization across source transport. The actual
refinement composition then identifies the final exchange on the supplied model.
-/

@[expose] public section
namespace CategoryTheory

variable {A B C D E : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
  {F : A ⥤ D} {P : D ⥤ E} {V : A ⥤ B} {W : B ⥤ C} {U : A ⥤ C}
  {R N : B ⥤ E} {R' N' Q : C ⥤ E}

/-- Normalize original exchange through actual source transport and actual refinements. -/
theorem cartesianExchangeNormalization
    (βraw : F ⋙ P ≅ V ⋙ R) (βdense : F ⋙ P ≅ V ⋙ N)
    (ψraw : R ≅ W ⋙ R') (ψdense : N ≅ W ⋙ N') (ψfinal : N ≅ W ⋙ Q)
    (c : U ≅ V ⋙ W) (d : R ⟶ N) (dt : R' ⟶ N') (r : N' ⟶ Q) (t : R' ⟶ Q)
    (βr : F ⋙ P ⟶ U ⋙ R') (βq : F ⋙ P ⟶ U ⋙ Q)
    (hb : βdense.hom = βraw.hom ≫ Functor.whiskerLeft V d)
    (hs : ψfinal.hom = ψdense.hom ≫ Functor.whiskerLeft W r)
    (hn : d ≫ ψdense.hom = ψraw.hom ≫ Functor.whiskerLeft W dt)
    (ht : dt ≫ r = t)
    (hr : (cartesianSourceExchange βraw ψraw c).hom = βr)
    (hq : βq = βr ≫ Functor.whiskerLeft U t) :
    (cartesianSourceExchange βdense ψfinal c).hom = βq := by
  apply NatTrans.ext
  funext K
  have hbK := congrArg (fun z => z.app K) hb
  have hsK := congrArg (fun z => z.app (V.obj K)) hs
  have hnK := congrArg (fun z => z.app (V.obj K)) hn
  have htK := congrArg (fun z => z.app (W.obj (V.obj K))) ht
  have hrK := congrArg (fun z => z.app K) hr
  have hqK := congrArg (fun z => z.app K) hq
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hbK hsK hnK htK hqK
  rw [cartesianSourceExchange_hom_app, hbK, hsK, hqK]
  simp only [Category.assoc]
  rw [← Category.assoc (d.app _) _ _, hnK]
  simp only [Category.assoc]
  rw [← Category.assoc (dt.app _) _ _, htK]
  have hnT := t.naturality (c.inv.app K)
  change R'.map (c.inv.app K) ≫ t.app (U.obj K) =
    t.app (W.obj (V.obj K)) ≫ Q.map (c.inv.app K) at hnT
  rw [← hnT, ← Category.assoc (ψraw.hom.app _) _ _]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ t.app (U.obj K))
      ((cartesianSourceExchange_hom_app βraw ψraw c K).symm.trans hrK)

end CategoryTheory
