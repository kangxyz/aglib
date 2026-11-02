/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Original identity-factorization contraction and source expansion -/

@[expose] public section
namespace CategoryTheory
variable {A B : Type*} [Category* A] [Category* B]
  {J I : A ⥤ A} {L : A ⥤ B}

/-- The original product identity and normalized source expansion give the actual source unit. -/
theorem identitySourceExpansion
    (eJ : J ≅ 𝟭 A) (eI : I ≅ 𝟭 A) (ε : J ⋙ I ≅ 𝟭 A) (c : L ≅ J ⋙ L)
    (he : ε = Functor.isoWhiskerRight eJ I ≪≫ Functor.leftUnitor I ≪≫ eI)
    (hc : c ≪≫ Functor.isoWhiskerRight eJ L ≪≫ Functor.leftUnitor L = Iso.refl L) :
    Functor.isoWhiskerRight ε L ≪≫ Functor.leftUnitor L ≪≫ c =
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft J eI ≪≫ Functor.rightUnitor J) L := by
  let z := Functor.isoWhiskerRight eJ L ≪≫ Functor.leftUnitor L
  have hc' : c = z.symm := by
    have ht := congrArg (fun a => a ≪≫ z.symm) hc
    change (c ≪≫ z) ≪≫ z.symm = _ at ht
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl, Iso.refl_trans] using ht
  subst ε
  rw [hc']
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [z, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.map_comp,
    Functor.id_obj, Category.id_comp]
  rw [L.map_id (I.obj K), L.map_id (J.obj K)]
  have hi : 𝟙 (L.obj K) ≫ L.map (eJ.inv.app K) = L.map (eJ.inv.app K) :=
    Category.id_comp _
  rw [hi]
  have hi' : 𝟙 (L.obj (I.obj K)) ≫
      (L.map (eI.hom.app K) ≫ L.map (eJ.inv.app K)) =
      L.map (eI.hom.app K) ≫ L.map (eJ.inv.app K) := Category.id_comp _
  have hi'' : L.map (eI.hom.app (J.obj K)) ≫ 𝟙 (L.obj (J.obj K)) =
      L.map (eI.hom.app (J.obj K)) := Category.comp_id _
  simp only [Category.assoc]
  rw [hi', hi'']
  have hn := eI.hom.naturality (eJ.hom.app K)
  change I.map (eJ.hom.app K) ≫ eI.hom.app K =
    eI.hom.app (J.obj K) ≫ eJ.hom.app K at hn
  have hn' : I.map (eJ.hom.app K) ≫ eI.hom.app K ≫ eJ.inv.app K =
      eI.hom.app (J.obj K) := by
    rw [← Category.assoc, hn, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id (eI.hom.app (J.obj K))
  simpa only [Functor.map_comp] using congrArg (fun t => L.map t) hn'

end CategoryTheory
