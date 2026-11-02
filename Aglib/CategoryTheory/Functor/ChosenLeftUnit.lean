/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionChoice

/-! # Descent of a proved supplied left-unit triangle through canonical comparisons -/

@[expose] public section
namespace CategoryTheory
variable {A B : Type*} [Category* A] [Category* B]
  {I P Q : A ⥤ A} {F H V W : A ⥤ B}

/-- Actual comparison squares transport the proved supplied triangle to the chosen unit law. -/
theorem chosenLeftUnit (κ : I ⋙ F ≅ H) (χI : I ≅ P) (χQ : I ≅ Q)
    (χF : F ≅ V) (χH : H ≅ W) (τ : P ≅ Q) (α : Q ⋙ V ≅ W)
    (ε : P ≅ 𝟭 A) (t : V ≅ W) (η : H ≅ F)
    (hsource : χI ≪≫ τ = χQ)
    (hκ : κ ≪≫ χH = compositionPairIso χQ χF ≪≫ α)
    (hmodel : Functor.isoWhiskerRight τ V ≪≫ α =
      Functor.isoWhiskerRight ε V ≪≫ Functor.leftUnitor V ≪≫ t)
    (htarget : η ≪≫ χF ≪≫ t = χH) :
    κ ≪≫ η = Functor.isoWhiskerRight (χI ≪≫ ε) F ≪≫ Functor.leftUnitor F := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (cancel_mono (χF.hom.app K ≫ t.hom.app K)).mp
  have hs := congrArg (fun e => e.hom.app K) hsource
  have hk := congrArg (fun e => e.hom.app K) hκ
  have hm := congrArg (fun e => e.hom.app K) hmodel
  have ht := congrArg (fun e => e.hom.app K) htarget
  change χI.hom.app K ≫ τ.hom.app K = χQ.hom.app K at hs
  simp only [compositionPairIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc] at hk
  change V.map (τ.hom.app K) ≫ α.hom.app K =
    V.map (ε.hom.app K) ≫ 𝟙 (V.obj K) ≫ t.hom.app K at hm
  have hi : 𝟙 (V.obj K) ≫ t.hom.app K = t.hom.app K := Category.id_comp _
  rw [hi] at hm
  change η.hom.app K ≫ χF.hom.app K ≫ t.hom.app K = χH.hom.app K at ht
  change (κ.hom.app K ≫ η.hom.app K) ≫ (χF.hom.app K ≫ t.hom.app K) =
    (F.map (χI.hom.app K ≫ ε.hom.app K) ≫ 𝟙 (F.obj K)) ≫
      (χF.hom.app K ≫ t.hom.app K)
  have hfi : F.map (χI.hom.app K ≫ ε.hom.app K) ≫ 𝟙 (F.obj K) =
      F.map (χI.hom.app K ≫ ε.hom.app K) := Category.comp_id _
  rw [hfi]
  rw [Category.assoc, ht, hk, ← hs, F.map_comp]
  have hnτ := χF.hom.naturality (τ.hom.app K)
  have hnε := χF.hom.naturality (ε.hom.app K)
  change F.map (τ.hom.app K) ≫ χF.hom.app (Q.obj K) =
    χF.hom.app (P.obj K) ≫ V.map (τ.hom.app K) at hnτ
  change F.map (ε.hom.app K) ≫ χF.hom.app K =
    χF.hom.app (P.obj K) ≫ V.map (ε.hom.app K) at hnε
  simp only [Category.assoc]
  rw [← Category.assoc (F.map (τ.hom.app K)), hnτ, Category.assoc, hm]
  rw [← Category.assoc (χF.hom.app (P.obj K)), ← hnε]
  simp only [Functor.map_comp, Category.assoc]

end CategoryTheory
