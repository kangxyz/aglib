/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceIsoBaseChange
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA' uD uD' uE uE' vA vA' vD vD' vE vE'

/-- Four original canonical model squares transport the actual interchange law. -/
theorem sourceIsoBaseChange_modelTransport
    {A : Type uA} {A' : Type uA'} {D : Type uD} {D' : Type uD'} {E : Type uE} {E' : Type uE'}
    [Category.{vA} A] [Category.{vA'} A'] [Category.{vD} D] [Category.{vD'} D']
    [Category.{vE} E] [Category.{vE'} E']
    {F Fm : A ⥤ E} {F' Fm' : A' ⥤ E} {G Gm : D ⥤ E'} {G' Gm' : D' ⥤ E'}
    {B : E ⥤ E'} {V : A ⥤ A'} {W : A ⥤ D} {W' : A' ⥤ D'} {V' : D ⥤ D'}
    (s : F ≅ V ⋙ F') (β' : F' ⋙ B ≅ W' ⋙ G') (β : F ⋙ B ≅ W ⋙ G)
    (s' : G ≅ V' ⋙ G') (c : V ⋙ W' ≅ W ⋙ V')
    (sm : Fm ≅ V ⋙ Fm') (βm' : Fm' ⋙ B ≅ W' ⋙ Gm') (βm : Fm ⋙ B ≅ W ⋙ Gm)
    (sm' : Gm ≅ V' ⋙ Gm') (a : F ≅ Fm) (a' : F' ≅ Fm')
    (d : G ≅ Gm) (d' : G' ≅ Gm')
    (hs : a ≪≫ sm = s ≪≫ Functor.isoWhiskerLeft V a')
    (hb' : Functor.isoWhiskerRight a' B ≪≫ βm' = β' ≪≫ Functor.isoWhiskerLeft W' d')
    (hb : Functor.isoWhiskerRight a B ≪≫ βm = β ≪≫ Functor.isoWhiskerLeft W d)
    (hs' : d ≪≫ sm' = s' ≪≫ Functor.isoWhiskerLeft V' d')
    (h : SourceIsoBaseChangeEquation sm βm'.hom βm.hom sm' c) :
    SourceIsoBaseChangeEquation s β'.hom β.hom s' c := by
  intro K
  have hsK := congrArg (fun z => z.hom.app K) hs
  have hb'K := congrArg (fun z => z.hom.app (V.obj K)) hb'
  have hbK := congrArg (fun z => z.hom.app K) hb
  have hs'K := congrArg (fun z => z.hom.app (W.obj K)) hs'
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj] at hsK hb'K hbK hs'K
  have hn := d'.hom.naturality (c.hom.app K)
  dsimp only [Functor.comp_obj] at hn
  apply (cancel_mono (d'.hom.app (V'.obj (W.obj K)))).mp
  simp only [Category.assoc]
  calc
    _ = B.map (s.hom.app K) ≫ β'.hom.app (V.obj K) ≫
        d'.hom.app (W'.obj (V.obj K)) ≫ Gm'.map (c.hom.app K) := by rw [hn]
    _ = B.map (s.hom.app K) ≫ B.map (a'.hom.app (V.obj K)) ≫
        βm'.hom.app (V.obj K) ≫ Gm'.map (c.hom.app K) := by
      simpa only [Category.assoc] using congrArg
        (fun z => B.map (s.hom.app K) ≫ z ≫ Gm'.map (c.hom.app K)) hb'K.symm
    _ = B.map (a.hom.app K) ≫ B.map (sm.hom.app K) ≫
        βm'.hom.app (V.obj K) ≫ Gm'.map (c.hom.app K) := by
      rw [← B.map_comp_assoc, ← hsK, B.map_comp, Category.assoc]
    _ = B.map (a.hom.app K) ≫ βm.hom.app K ≫ sm'.hom.app (W.obj K) := by rw [h K]
    _ = β.hom.app K ≫ d.hom.app (W.obj K) ≫ sm'.hom.app (W.obj K) := by
      rw [← Category.assoc, hbK, Category.assoc]
    _ = _ := by rw [hs'K]

end CategoryTheory
