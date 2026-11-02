/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionChoice

/-! # Descent of the proved supplied right-unit triangle through original comparisons -/

@[expose] public section
namespace CategoryTheory
variable {A B : Type*} [Category* A] [Category* B]
  {I P : B ⥤ B} {F H Q V : A ⥤ B}

/-- The actual supplied triangle and canonical comparison squares imply the chosen unit equation. -/
theorem chosenRightUnit (κ : F ⋙ I ≅ H) (χF : F ≅ Q) (χI : I ≅ P)
    (χH : H ≅ V) (α : Q ⋙ P ≅ V) (t : V ≅ Q) (ε : P ≅ 𝟭 B) (η : H ≅ F)
    (hκ : κ ≪≫ χH = compositionPairIso χF χI ≪≫ α)
    (hmodel : α ≪≫ t = Functor.isoWhiskerLeft Q ε ≪≫ Functor.rightUnitor Q)
    (htarget : η ≪≫ χF = χH ≪≫ t) :
    κ ≪≫ η = Functor.isoWhiskerLeft F (χI ≪≫ ε) ≪≫ Functor.rightUnitor F := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (cancel_mono (χF.hom.app K)).mp
  have hk := congrArg (fun e => e.hom.app K) hκ
  have hm := congrArg (fun e => e.hom.app K) hmodel
  have ht := congrArg (fun e => e.hom.app K) htarget
  simp only [compositionPairIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc] at hk
  change α.hom.app K ≫ t.hom.app K = ε.hom.app (Q.obj K) ≫ 𝟙 (Q.obj K) at hm
  have hmi : ε.hom.app (Q.obj K) ≫ 𝟙 (Q.obj K) = ε.hom.app (Q.obj K) := Category.comp_id _
  rw [hmi] at hm
  change η.hom.app K ≫ χF.hom.app K = χH.hom.app K ≫ t.hom.app K at ht
  change (κ.hom.app K ≫ η.hom.app K) ≫ χF.hom.app K =
    ((χI.hom.app (F.obj K) ≫ ε.hom.app (F.obj K)) ≫ 𝟙 (F.obj K)) ≫ χF.hom.app K
  have hi : (χI.hom.app (F.obj K) ≫ ε.hom.app (F.obj K)) ≫ 𝟙 (F.obj K) =
      χI.hom.app (F.obj K) ≫ ε.hom.app (F.obj K) := Category.comp_id _
  rw [hi, Category.assoc, ht, ← Category.assoc, hk]
  have hnI := χI.hom.naturality (χF.hom.app K)
  have hnε := ε.hom.naturality (χF.hom.app K)
  change I.map (χF.hom.app K) ≫ χI.hom.app (Q.obj K) =
    χI.hom.app (F.obj K) ≫ P.map (χF.hom.app K) at hnI
  change P.map (χF.hom.app K) ≫ ε.hom.app (Q.obj K) =
    ε.hom.app (F.obj K) ≫ χF.hom.app K at hnε
  simp only [Category.assoc]
  rw [hm, ← Category.assoc (I.map (χF.hom.app K)), hnI, Category.assoc, hnε]

end CategoryTheory
