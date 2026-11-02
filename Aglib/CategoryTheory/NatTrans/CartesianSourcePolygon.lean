/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CartesianSourcePasting
public import Aglib.CategoryTheory.NatTrans.CartesianSourceTargetTransport
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA' uD uD' uD'' uL₁ uA₁ uL₂ uA₂ uLs vA vA' vD vD' vD'' vL₁ vA₁ vL₂ vA₂ vLs

section Target
variable {A : Type uA} {A' : Type uA'} {D : Type uD} {D' : Type uD'} {D'' : Type uD''}
  [Category.{vA} A] [Category.{vA'} A'] [Category.{vD} D] [Category.{vD'} D'] [Category.{vD''} D'']
  {V : A ⥤ A'} {W : A ⥤ D} {W' : A' ⥤ D'} {V' : D ⥤ D'}
  {T : D' ⥤ D''} {U : A' ⥤ D''} {Q : D ⥤ D''}
  {J : A ⥤ D''} {M : A ⥤ D'}

/-- The two original associativity faces contract the target source polygon. -/
theorem cartesianPastingTargetSourceIso_of_assoc
    (c₁ : M ≅ V ⋙ W') (c₂ : M ≅ W ⋙ V')
    (q : U ≅ W' ⋙ T) (d : Q ≅ V' ⋙ T)
    (L : J ≅ V ⋙ U) (R : J ≅ W ⋙ Q) (E : J ≅ M ⋙ T)
    (h₁ : L ≪≫ Functor.isoWhiskerLeft V q =
      E ≪≫ Functor.isoWhiskerRight c₁ T ≪≫ Functor.associator V W' T)
    (h₂ : R ≪≫ Functor.isoWhiskerLeft W d =
      E ≪≫ Functor.isoWhiskerRight c₂ T ≪≫ Functor.associator W V' T) :
    cartesianPastingTargetSourceIso (c₁.symm ≪≫ c₂) q d = L.symm ≪≫ R := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have h₁K := congrArg (fun i => i.hom.app K) h₁
  have h₂K := congrArg (fun i => i.hom.app K) h₂
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at h₁K h₂K
  apply (cancel_epi (L.hom.app K)).mp
  simp only [cartesianPastingTargetSourceIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc, T.map_comp,
    Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% h₁K]
  rw [← T.map_comp_assoc, Iso.hom_inv_id_app, T.map_id, Category.id_comp]
  rw [← reassoc_of% h₂K, Iso.hom_inv_id_app]
  exact Category.comp_id _

end Target

section Full
variable {A : Type uA} {L₁ : Type uL₁} {A₁ : Type uA₁} {L₂ : Type uL₂} {A₂ : Type uA₂}
  {Ls : Type uLs}
  [Category.{vA} A] [Category.{vL₁} L₁] [Category.{vA₁} A₁] [Category.{vL₂} L₂]
  [Category.{vA₂} A₂] [Category.{vLs} Ls]
  {V₁ : A ⥤ L₁} {E₁ : L₁ ⥤ A₁} {W₁ : A ⥤ A₁}
  {V₂ : L₁ ⥤ L₂} {W₂ : A₁ ⥤ A₂} {Q : L₂ ⥤ A₂}
  {Vs : A ⥤ Ls} {Es : Ls ⥤ L₂} {Et : Ls ⥤ A₂}
  {H : A ⥤ L₂} {Ht : A ⥤ A₂} {J : L₁ ⥤ A₂}

/-- Three original associativity faces contract the full source polygon. -/
theorem cartesianPastingSourceIso_of_assoc
    (B : Ht ≅ V₁ ⋙ J) (C : Ht ≅ H ⋙ Q)
    (L : J ≅ E₁ ⋙ W₂) (R : J ≅ V₂ ⋙ Q)
    (δ : H ≅ V₁ ⋙ V₂) (η : H ≅ Vs ⋙ Es)
    (δt : Ht ≅ W₁ ⋙ W₂) (ηt : Ht ≅ Vs ⋙ Et)
    (q : W₁ ≅ V₁ ⋙ E₁) (d : Et ≅ Es ⋙ Q)
    (hA : B ≪≫ Functor.isoWhiskerLeft V₁ L =
      δt ≪≫ Functor.isoWhiskerRight q W₂ ≪≫ Functor.associator V₁ E₁ W₂)
    (hB : B ≪≫ Functor.isoWhiskerLeft V₁ R =
      C ≪≫ Functor.isoWhiskerRight δ Q ≪≫ Functor.associator V₁ V₂ Q)
    (hC : ηt ≪≫ Functor.isoWhiskerLeft Vs d =
      C ≪≫ Functor.isoWhiskerRight η Q ≪≫ Functor.associator Vs Es Q) :
    cartesianPastingSourceIso q (L.symm ≪≫ R) (δ.symm ≪≫ η) d = δt.symm ≪≫ ηt := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hAK := congrArg (fun i => i.hom.app K) hA
  have hBK := congrArg (fun i => i.hom.app K) hB
  have hCK := congrArg (fun i => i.hom.app K) hC
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at hAK hBK hCK
  apply (cancel_epi (δt.hom.app K)).mp
  simp only [cartesianPastingSourceIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc, Q.map_comp,
    Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hAK, Iso.hom_inv_id_app_assoc, reassoc_of% hBK]
  rw [← Q.map_comp_assoc, Iso.hom_inv_id_app, Q.map_id, Category.id_comp]
  rw [← reassoc_of% hCK, Iso.hom_inv_id_app]
  exact Category.comp_id _

end Full

end CategoryTheory
