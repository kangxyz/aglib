/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CartesianSourceExchange
public import Aglib.CategoryTheory.NatTrans.SourceIsoBaseChange
public import Aglib.CategoryTheory.NatTrans.SourceIsoComposition
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA' uD uD' uD'' uE uE' vA vA' vD vD' vD'' vE vE'

variable {A : Type uA} {A' : Type uA'} {D : Type uD} {D' : Type uD'} {D'' : Type uD''}
  {E : Type uE} {E' : Type uE'}
  [Category.{vA} A] [Category.{vA'} A'] [Category.{vD} D] [Category.{vD'} D'] [Category.{vD''} D'']
  [Category.{vE} E] [Category.{vE'} E']
  {F : A ⥤ E} {F' : A' ⥤ E} {G : D ⥤ E'} {G' : D' ⥤ E'} {G'' : D'' ⥤ E'}
  {B : E ⥤ E'} {V : A ⥤ A'} {W : A ⥤ D} {W' : A' ⥤ D'} {V' : D ⥤ D'}
  {T : D' ⥤ D''} {U : A' ⥤ D''} {Q : D ⥤ D''}

/-- The actual source polygon for a further target presentation. -/
def cartesianPastingTargetSourceIso
    (c : V ⋙ W' ≅ W ⋙ V') (q : U ≅ W' ⋙ T) (d : Q ≅ V' ⋙ T) :
    V ⋙ U ≅ W ⋙ Q :=
  Functor.isoWhiskerLeft V q ≪≫ (Functor.associator V W' T).symm ≪≫
    Functor.isoWhiskerRight c T ≪≫ Functor.associator W V' T ≪≫
    Functor.isoWhiskerLeft W d.symm

theorem targetSource_hom_app
    (c : V ⋙ W' ≅ W ⋙ V') (q : U ≅ W' ⋙ T) (d : Q ≅ V' ⋙ T) (K : A) :
    (cartesianPastingTargetSourceIso c q d).hom.app K =
      q.hom.app (V.obj K) ≫ T.map (c.hom.app K) ≫ d.inv.app (W.obj K) := by
  simp only [cartesianPastingTargetSourceIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Category.id_comp]

/-- A genuine source/base-change square remains genuine after the original target
source transport. The new comparison is identified by its proved source composition law. -/
theorem sourceIsoBaseChange_targetTransport
    (s : F ≅ V ⋙ F') (β' : F' ⋙ B ≅ W' ⋙ G') (β : F ⋙ B ⟶ W ⋙ G)
    (s' : G ≅ V' ⋙ G') (c : V ⋙ W' ≅ W ⋙ V')
    (t : G' ≅ T ⋙ G'') (q : U ≅ W' ⋙ T)
    (r : G ≅ Q ⋙ G'') (d : Q ≅ V' ⋙ T)
    (hb : SourceIsoBaseChangeEquation s β'.hom β s' c)
    (hs : SourceIsoCompositionEquation s' t r (𝟙 G'') d) :
    SourceIsoBaseChangeEquation s (cartesianSourceExchange β' t q).hom β r
      (cartesianPastingTargetSourceIso c q d) := by
  intro K
  have hsK := hs (W.obj K)
  dsimp only [Functor.comp_obj, NatTrans.id_app] at hsK
  simp only [Category.id_comp] at hsK
  have hn := t.hom.naturality (c.hom.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [cartesianSourceExchange_hom_app, targetSource_hom_app]
  simp only [G''.map_comp, Category.assoc]
  have hq : G''.map (q.inv.app (V.obj K)) ≫ G''.map (q.hom.app (V.obj K)) = 𝟙 _ := by
    rw [← G''.map_comp, Iso.inv_hom_id_app, G''.map_id]
  calc
    _ = B.map (s.hom.app K) ≫ β'.hom.app (V.obj K) ≫
        t.hom.app (W'.obj (V.obj K)) ≫ G''.map (T.map (c.hom.app K)) ≫
        G''.map (d.inv.app (W.obj K)) := by
      rw [← Category.assoc (G''.map (q.inv.app (V.obj K))), hq, Category.id_comp]
    _ = B.map (s.hom.app K) ≫ β'.hom.app (V.obj K) ≫
        G'.map (c.hom.app K) ≫ t.hom.app (V'.obj (W.obj K)) ≫
        G''.map (d.inv.app (W.obj K)) := by
      simpa only [Category.assoc] using congrArg
        (fun z => B.map (s.hom.app K) ≫ β'.hom.app (V.obj K) ≫ z ≫
          G''.map (d.inv.app (W.obj K))) hn.symm
    _ = β.app K ≫ s'.hom.app (W.obj K) ≫ t.hom.app (V'.obj (W.obj K)) ≫
        G''.map (d.inv.app (W.obj K)) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ t.hom.app (V'.obj (W.obj K)) ≫
          G''.map (d.inv.app (W.obj K))) (hb K)
    _ = β.app K ≫ r.hom.app (W.obj K) := by
      rw [← Category.assoc (s'.hom.app _), ← hsK]
      simp only [Category.assoc, ← G''.map_comp, Iso.hom_inv_id_app,
        G''.map_id, Category.comp_id]

end CategoryTheory
