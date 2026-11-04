/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.ShiftedHom
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! Transport and regrading of the original inverse shift adjunct. -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]

/-- Shift regrading commutes with the original functor shift comparison. -/
theorem shiftAdjunctionHomEquiv_map {U K : C} (q : ℤ)
    (j : U⟦-q⟧ ⟶ K) :
    ((shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction.homEquiv (F.obj U) (F.obj K))
        ((F.commShiftIso (-q)).inv.app U ≫ F.map j) =
      ShiftedHom.map
        ((shiftEquiv' C (-q) q (neg_add_cancel q)).toAdjunction.homEquiv U K j) F := by
  let a := F.commShiftIso (-q)
  let b := F.commShiftIso q
  let ai : (F.obj U)⟦-q⟧ ⟶ F.obj (U⟦-q⟧) := a.inv.app U
  let G := shiftFunctor D q
  let bU : F.obj ((U⟦-q⟧)⟦q⟧) ⟶ G.obj (F.obj (U⟦-q⟧)) := b.hom.app (U⟦-q⟧)
  let Z := shiftFunctorZero C ℤ
  let Z' := shiftFunctorZero D ℤ
  let A := shiftFunctorAdd' C (-q) q 0 (neg_add_cancel q)
  let B := shiftFunctorAdd' D (-q) q 0 (neg_add_cancel q)
  let adjC := (shiftEquiv' C (-q) q (neg_add_cancel q)).toAdjunction
  let adjD := (shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction
  have h := congrArg (fun i => i.hom.app U) (F.commShiftIso_add' (neg_add_cancel q))
  simp only [F.commShiftIso_zero ℤ, Functor.CommShift.isoZero_hom_app,
    Functor.CommShift.isoAdd'_hom_app] at h
  change F.map (Z.hom.app U) ≫ Z'.inv.app (F.obj U) =
    F.map (A.hom.app U) ≫ b.hom.app (U⟦-q⟧) ≫ a.hom.app U⟦q⟧' ≫ B.inv.app (F.obj U) at h
  have hU : adjD.unit.app (F.obj U) ≫ a.inv.app U⟦q⟧' =
      F.map (adjC.unit.app U) ≫ b.hom.app (U⟦-q⟧) := by
    change (Z'.inv.app (F.obj U) ≫ B.hom.app (F.obj U)) ≫ a.inv.app U⟦q⟧' =
      F.map (Z.inv.app U ≫ A.hom.app U) ≫ b.hom.app (U⟦-q⟧)
    have hp := congrArg (fun z => F.map (Z.inv.app U) ≫ z ≫
      B.hom.app (F.obj U) ≫ a.inv.app U⟦q⟧') h
    simp only [Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id_app,
      Iso.inv_hom_id_app_assoc, F.map_id, Category.id_comp] at hp
    have ha : (shiftFunctor D q).map (a.hom.app U) ≫
        (shiftFunctor D q).map (a.inv.app U) = 𝟙 _ := by
      rw [← (shiftFunctor D q).map_comp, a.hom_inv_id_app, (shiftFunctor D q).map_id]
    rw [ha] at hp
    exact (Category.assoc _ _ _).trans
      (hp.trans (congrArg (fun z => F.map (Z.inv.app U ≫ A.hom.app U) ≫ z)
        (Category.comp_id bU)))
  change adjD.homEquiv (F.obj U) (F.obj K) (ai ≫ F.map j) =
    F.map (adjC.homEquiv U K j) ≫ b.hom.app K
  have hC : adjC.homEquiv U K j = adjC.unit.app U ≫ (shiftFunctor C q).map j :=
    adjC.homEquiv_unit U K j
  have hD : adjD.homEquiv (F.obj U) (F.obj K) (ai ≫ F.map j) =
      adjD.unit.app (F.obj U) ≫ G.map (ai ≫ F.map j) :=
    adjD.homEquiv_unit (F.obj U) (F.obj K) (ai ≫ F.map j)
  let iC : U ⟶ (U⟦-q⟧)⟦q⟧ := adjC.unit.app U
  let iD : F.obj U ⟶ ((F.obj U)⟦-q⟧)⟦q⟧ := adjD.unit.app (F.obj U)
  have he : iD ≫ G.map ai = F.map iC ≫ bU := hU
  have hn : F.map (j⟦q⟧') ≫ b.hom.app K = bU ≫ G.map (F.map j) :=
    F.commShiftIso_hom_naturality j q
  have h₁ : iD ≫ G.map (ai ≫ F.map j) = (iD ≫ G.map ai) ≫ G.map (F.map j) :=
    (congrArg (fun x => iD ≫ x) (G.map_comp ai (F.map j))).trans
      (Category.assoc _ _ _).symm
  have h₂ : (iD ≫ G.map ai) ≫ G.map (F.map j) = (F.map iC ≫ bU) ≫ G.map (F.map j) :=
    congrArg (fun (x : F.obj U ⟶ G.obj (F.obj (U⟦-q⟧))) => x ≫ G.map (F.map j)) he
  have h₃ : (F.map iC ≫ bU) ≫ G.map (F.map j) = (F.map iC ≫ F.map (j⟦q⟧')) ≫ b.hom.app K :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun x => F.map iC ≫ x) hn.symm).trans (Category.assoc _ _ _).symm)
  have h₄ : (F.map iC ≫ F.map (j⟦q⟧')) ≫ b.hom.app K =
      F.map (iC ≫ j⟦q⟧') ≫ b.hom.app K :=
    congrArg (fun x => x ≫ b.hom.app K) (F.map_comp iC (j⟦q⟧')).symm
  exact hD.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans
    (congrArg (fun x => F.map x ≫ b.hom.app K) hC.symm)))))

/-- The inverse shift adjunction is transported by the original shift comparison. -/
theorem shiftAdjunctionInverse_map {U K : C} (q : ℤ) (z : ShiftedHom U K q) :
    (F.commShiftIso (-q)).inv.app U ≫ F.map
      (((shiftEquiv' C (-q) q (neg_add_cancel q)).toAdjunction.homEquiv U K).symm z) =
    (((shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction.homEquiv (F.obj U) (F.obj K)).symm
      (z.map F)) := by
  let ac := (shiftEquiv' C (-q) q (neg_add_cancel q)).toAdjunction
  let ad := (shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction
  let j : U⟦-q⟧ ⟶ K := (ac.homEquiv U K).symm z
  apply (ad.homEquiv (F.obj U) (F.obj K)).injective
  change ad.homEquiv (F.obj U) (F.obj K) ((F.commShiftIso (-q)).inv.app U ≫ F.map j) =
    ad.homEquiv (F.obj U) (F.obj K) ((ad.homEquiv (F.obj U) (F.obj K)).symm (z.map F))
  have h : ac.homEquiv U K j = z := (ac.homEquiv U K).apply_symm_apply z
  exact (F.shiftAdjunctionHomEquiv_map q j).trans
    ((congrArg (fun y : ShiftedHom U K q => y.map F) h).trans
      ((ad.homEquiv (F.obj U) (F.obj K)).apply_symm_apply (z.map F)).symm)

/-- Transport an original grade single through the original shifted degree-zero unit. -/
noncomputable def shiftedSingleIsoOfIso {U Uq : C} {V Vq : D} (q : ℤ)
    (η : U⟦-q⟧ ≅ Uq) (η' : V⟦-q⟧ ≅ Vq) (u : F.obj U ≅ V) :
    F.obj Uq ≅ Vq :=
  F.mapIso η.symm ≪≫ (F.commShiftIso (-q)).app U ≪≫
    (shiftFunctor D (-q)).mapIso u ≪≫ η'

/-- The transported original graded component is the inverse shift adjunct
of the same pulled-back shifted class, with the specified source and target maps. -/
theorem shiftedSingleIsoOfIso_inv_comp {U Uq K : C} {V Vq K' : D} (q : ℤ)
    (η : U⟦-q⟧ ≅ Uq) (η' : V⟦-q⟧ ≅ Vq) (u : F.obj U ≅ V)
    (w : F.obj K ⟶ K') (y : ShiftedHom U K q) :
    (F.shiftedSingleIsoOfIso q η η' u).inv ≫
      F.map (η.inv ≫ ((shiftEquiv' C (-q) q (neg_add_cancel q)).toAdjunction.homEquiv U K).symm y) ≫
        w =
    η'.inv ≫ ((shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction.homEquiv V K').symm
      (u.inv ≫ y.map F ≫ w⟦q⟧') := by
  let adj := (shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction
  let j : U⟦-q⟧ ⟶ K :=
    ((shiftEquiv' C (-q) q (neg_add_cancel q)).toAdjunction.homEquiv U K).symm y
  change (F.shiftedSingleIsoOfIso q η η' u).inv ≫ F.map (η.inv ≫ j) ≫ w = _
  simp only [shiftedSingleIsoOfIso, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
    Iso.symm_inv, Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc η.hom η.inv, η.hom_inv_id, F.map_id, Category.id_comp]
  have h := F.shiftAdjunctionInverse_map q y
  change (F.commShiftIso (-q)).inv.app U ≫ F.map j =
    (adj.homEquiv (F.obj U) (F.obj K)).symm (y.map F) at h
  rw [reassoc_of% h]
  have hU : (adj.homEquiv V (F.obj K)).symm (u.inv ≫ y.map F) =
      (shiftFunctor D (-q)).map u.inv ≫ (adj.homEquiv (F.obj U) (F.obj K)).symm (y.map F) :=
    adj.homEquiv_naturality_left_symm u.inv (y.map F)
  have hUw : (shiftFunctor D (-q)).map u.inv ≫
        (adj.homEquiv (F.obj U) (F.obj K)).symm (y.map F) ≫ w =
      (adj.homEquiv V (F.obj K)).symm (u.inv ≫ y.map F) ≫ w :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ w) hU.symm)
  have hw : (adj.homEquiv V K').symm ((u.inv ≫ y.map F) ≫ w⟦q⟧') =
      (adj.homEquiv V (F.obj K)).symm (u.inv ≫ y.map F) ≫ w :=
    adj.homEquiv_naturality_right_symm (u.inv ≫ y.map F) w
  have hT : (adj.homEquiv V K').symm (u.inv ≫ y.map F ≫ w⟦q⟧') =
      (adj.homEquiv V (F.obj K)).symm (u.inv ≫ y.map F) ≫ w :=
    (congrArg (adj.homEquiv V K').symm (Category.assoc _ _ _).symm).trans hw
  exact congrArg (fun z => η'.inv ≫ z) (hUw.trans hT.symm)


end CategoryTheory.Functor

namespace CategoryTheory

variable {D : Type*} [Category* D] [HasShift D ℤ]
  {X U Uq K : D} {p q d : ℤ} (h : q + p = d)

/-- Undo the negative shift by the original shift adjunction and then
regrade to the total degree. -/
theorem shiftAdjunctionInverse_core (y : ShiftedHom U K q) :
    (shiftFunctorAdd' D (-q) d p (by omega)).hom.app U ≫
      (((shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction.homEquiv U K).symm y)⟦d⟧' =
    y⟦p⟧' ≫ (shiftFunctorAdd' D q p d h).inv.app K := by
  let A := shiftFunctorAdd' D (-q) d p (by omega)
  let B := shiftFunctorAdd' D q p d h
  let N := shiftFunctorAdd' D q (-q) 0 (add_neg_cancel q)
  let Z := shiftFunctorAdd' D 0 d d (zero_add d)
  let adj := (shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction
  let y' : U ⟶ (shiftEquiv' D (-q) q (neg_add_cancel q)).inverse.obj K := y
  have hj : (adj.homEquiv U K).symm y =
      (shiftFunctor D (-q)).map y ≫
        (shiftFunctorCompIsoId D q (-q) (add_neg_cancel q)).hom.app K := by
    exact adj.homEquiv_symm_apply U K y'
  have hAssoc := shiftFunctorAdd'_assoc_inv_app q (-q) d 0 p d
    (add_neg_cancel q) (by omega) (by omega) K
  have hC : ((shiftFunctorCompIsoId D q (-q) (add_neg_cancel q)).hom.app K)⟦d⟧' =
      N.inv.app K⟦d⟧' ≫ Z.inv.app K := by
    change (shiftFunctor D d).map
      (N.inv.app K ≫ (shiftFunctorZero D ℤ).hom.app K) = _
    rw [Functor.map_comp, shiftFunctorAdd'_zero_add_inv_app]
  rw [hj, Functor.map_comp, hC]
  have hn := (A.hom.naturality y).symm
  change A.hom.app U ≫ ((shiftFunctor D (-q)).map y)⟦d⟧' =
    y⟦p⟧' ≫ A.hom.app (K⟦q⟧) at hn
  rw [← Category.assoc (A.hom.app U)
    (((shiftFunctor D (-q)).map y)⟦d⟧') _]
  rw [hn]
  have hc : A.hom.app (K⟦q⟧) ≫ N.inv.app K⟦d⟧' ≫ Z.inv.app K = B.inv.app K := by
    apply (cancel_epi (A.inv.app (K⟦q⟧))).mp
    simp only [← Category.assoc]
    rw [A.inv_hom_id_app, Category.id_comp]
    exact hAssoc
  calc
    _ = y⟦p⟧' ≫
      (A.hom.app (K⟦q⟧) ≫ N.inv.app K⟦d⟧' ≫ Z.inv.app K) := by
        simp only [Category.assoc]
    _ = _ := by rw [hc]

/-- The given original grade-`q` unit iso and the total-shift iso identify
the inserted component with original shifted composition. -/
theorem shiftAdjunctionInverse_comp
    (η : U⟦-q⟧ ≅ Uq) (T : Uq⟦d⟧ ≅ U⟦p⟧)
    (hT : η.hom⟦d⟧' ≫ T.hom =
      (shiftFunctorAdd' D (-q) d p (by omega)).inv.app U)
    (x : ShiftedHom X U p) (y : ShiftedHom U K q) :
    x ≫ T.inv ≫
      (η.inv ≫ ((shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction.homEquiv U K).symm y)⟦d⟧' =
    x.comp y h := by
  let A := shiftFunctorAdd' D (-q) d p (by omega)
  let E := shiftEquiv' D (-q) q (neg_add_cancel q)
  let y' : U ⟶ E.inverse.obj K := y
  let z : U⟦-q⟧ ⟶ K := (E.toAdjunction.homEquiv U K).symm y'
  have hTi : T.inv = A.hom.app U ≫ η.hom⟦d⟧' := by
    apply (cancel_mono T.hom).mp
    rw [Category.assoc, hT, A.hom_inv_id_app, T.inv_hom_id]
  change x ≫ T.inv ≫ (η.inv ≫ z)⟦d⟧' = x.comp y h
  rw [hTi, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp]
  have hcancel : η.hom ≫ η.inv ≫ z = z := by
    rw [← Category.assoc, η.hom_inv_id, Category.id_comp]
  rw [hcancel]
  have hc := shiftAdjunctionInverse_core h y
  change A.hom.app U ≫ z⟦d⟧' =
    y⟦p⟧' ≫ (shiftFunctorAdd' D q p d h).inv.app K at hc
  rw [hc]
  rfl

end CategoryTheory

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}
  [R₁.CommShift ℤ] [R₂.CommShift ℤ] [U.CommShift ℤ] [V.CommShift ℤ]

/-- The normalized mate carries an original regraded adjunct to the corresponding
regraded adjunct of the transported original class. -/
theorem shiftedSingleIsoOfIso_inv_comp_mate (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (s : TwoSquare U L₁ L₂ V) (d : R₁ ⋙ U ⟶ V ⋙ R₂)
    [NatTrans.CommShift d ℤ] (hd : (mateEquiv adj₁ adj₂ s).natTrans = d)
    {I Iq : A} {J : B} {I' Iq' : C} {J' : D} {K : B} {K' : D}
    (e : L₁.obj I ≅ J) (e' : L₂.obj I' ≅ J')
    (u : U.obj I ≅ I') (v : V.obj J ≅ J') (t : V.obj K ≅ K')
    (h : s.app I ≫ V.map e.hom ≫ v.hom = L₂.map u.hom ≫ e'.hom)
    {q : ℤ} (η : I⟦-q⟧ ≅ Iq) (η' : I'⟦-q⟧ ≅ Iq')
    (x : ShiftedHom J K q) :
    (U.shiftedSingleIsoOfIso q η η' u).inv ≫ U.map
        (η.inv ≫ ((shiftEquiv' A (-q) q (neg_add_cancel q)).toAdjunction.homEquiv I
          (R₁.obj K)).symm (adj₁.shiftedHomEquiv q I K (e.hom ≫ x))) ≫
      d.app K ≫ R₂.map t.hom =
    η'.inv ≫ ((shiftEquiv' C (-q) q (neg_add_cancel q)).toAdjunction.homEquiv I'
      (R₂.obj K')).symm
        (adj₂.shiftedHomEquiv q I' K' (e'.hom ≫ v.inv ≫ x.map V ≫ t.hom⟦q⟧')) := by
  let w : U.obj (R₁.obj K) ⟶ R₂.obj K' := d.app K ≫ R₂.map t.hom
  let y := adj₁.shiftedHomEquiv q I K (e.hom ≫ x)
  have hr := U.shiftedSingleIsoOfIso_inv_comp q η η' u w y
  change (U.shiftedSingleIsoOfIso q η η' u).inv ≫ U.map
    (η.inv ≫ ((shiftEquiv' A (-q) q (neg_add_cancel q)).toAdjunction.homEquiv I
      (R₁.obj K)).symm y) ≫ w = _
  rw [hr]
  have hm := shiftedHomEquiv_of_mate_of_unitSquare adj₁ adj₂ s d hd e e' u v t h x
  have hw : w⟦q⟧' = (d.app K)⟦q⟧' ≫ (R₂.map t.hom)⟦q⟧' :=
    (shiftFunctor C q).map_comp (d.app K) (R₂.map t.hom)
  rw [hw]
  have h' : u.inv ≫ y.map U ≫ (d.app K)⟦q⟧' ≫ (R₂.map t.hom)⟦q⟧' =
      adj₂.shiftedHomEquiv q I' K' (e'.hom ≫ v.inv ≫ x.map V ≫ t.hom⟦q⟧') := hm
  exact congrArg (fun z : ShiftedHom I' (R₂.obj K') q =>
    η'.inv ≫ ((shiftEquiv' C (-q) q (neg_add_cancel q)).toAdjunction.homEquiv I'
      (R₂.obj K')).symm z) h'

end CategoryTheory
