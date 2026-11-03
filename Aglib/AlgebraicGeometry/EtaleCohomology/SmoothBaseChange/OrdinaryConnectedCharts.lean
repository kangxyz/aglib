/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedBaseChangeSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.OrdinaryChartGeometry
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageMate

/-! # Original ordinary exchange on connected local charts

The original horizontal unit equation and original presheaf naturality
identify the canonical mate on the given test. Both original unit section
maps are invertible by connected pullback. The total-space chart is the
existing site-square construction, with its actual cartesian projection.
No composite replacement exchange or conservative direct-image premise occurs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

/-- Original restriction naturality pastes the horizontal unit equation.
All section maps are evaluated in the same supplied presheaves and site functor. -/
private theorem originalUnit_restriction_paste
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (P : Cᵒᵖ ⥤ E) (Q : Dᵒᵖ ⥤ E) (β : P ⟶ R.op ⋙ Q)
    {U T : C} {V : D} {A : E} (a : T ⟶ U) (σ : R.obj U ⟶ V)
    (u : A ⟶ P.obj (op U)) (v : A ⟶ Q.obj (op V))
    (h : v ≫ Q.map σ.op = u ≫ β.app (op U)) :
    (u ≫ P.map a.op) ≫ β.app (op T) =
      v ≫ Q.map (R.map a ≫ σ).op := by
  calc
    (u ≫ P.map a.op) ≫ β.app (op T) =
        u ≫ (P.map a.op ≫ β.app (op T)) := Category.assoc _ _ _
    _ = u ≫ (β.app (op U) ≫ Q.map (R.map a).op) := by
      exact congrArg (fun k => u ≫ k) (β.naturality a.op)
    _ = (v ≫ Q.map σ.op) ≫ Q.map (R.map a).op := by
      rw [← Category.assoc, ← h]
    _ = v ≫ Q.map (R.map a ≫ σ).op := by
      simp only [op_comp, Q.map_comp, Category.assoc]

/-- Invertible original unit restrictions detect the literal mate component. -/
theorem originalMate_component_isIso_of_units
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (P : Cᵒᵖ ⥤ E) (Q : Dᵒᵖ ⥤ E) (β : P ⟶ R.op ⋙ Q)
    {U T : C} {V : D} {A : E} (a : T ⟶ U) (σ : R.obj U ⟶ V)
    (u : A ⟶ P.obj (op U)) (v : A ⟶ Q.obj (op V))
    [hu : IsIso (u ≫ P.map a.op)] [hv : IsIso (v ≫ Q.map (R.map a ≫ σ).op)]
    (h : v ≫ Q.map σ.op = u ≫ β.app (op U)) : IsIso (β.app (op T)) := by
  have he := originalUnit_restriction_paste R P Q β a σ u v h
  have : IsIso ((u ≫ P.map a.op) ≫ β.app (op T)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (u ≫ P.map a.op) (β.app (op T))

/-- Evaluate the original continuous-site horizontal unit square before
specializing its site functors. The native pushforward section comparisons
have identity components, so their original section carriers remain unchanged. -/
theorem originalContinuousSquare_unit_evaluation
    {C D C' D' E : Type*}
    [Category C] [Category D] [Category C'] [Category D'] [Category E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (r : C ⥤ D) (s : C ⥤ C') (t : D ⥤ D') (v : C' ⥤ D')
    [r.IsContinuous J K] [s.IsContinuous J J']
    [t.IsContinuous K K'] [v.IsContinuous J' K']
    [(s ⋙ v).IsContinuous J K'] [(r ⋙ t).IsContinuous J K']
    (σ : s ⋙ v ⟶ r ⋙ t)
    (δ : t.sheafPushforwardContinuous E K K' ⋙ r.sheafPushforwardContinuous E J K ⟶
      v.sheafPushforwardContinuous E J' K' ⋙ s.sheafPushforwardContinuous E J J')
    (hδ : δ = Functor.sheafPushforwardContinuousNatTrans σ E J K')
    (F : Sheaf K E) (G : Sheaf J' E) (H : Sheaf K' E)
    (uX : F ⟶ (t.sheafPushforwardContinuous E K K').obj H)
    (uS : (r.sheafPushforwardContinuous E J K).obj F ⟶
      (s.sheafPushforwardContinuous E J J').obj G)
    (β : G ⟶ (v.sheafPushforwardContinuous E J' K').obj H)
    (h : (r.sheafPushforwardContinuous E J K).map uX ≫ δ.app H =
      uS ≫ (s.sheafPushforwardContinuous E J J').map β)
    (U : C) :
    uX.hom.app (op (r.obj U)) ≫ H.obj.map (σ.app U).op =
      uS.hom.app (op U) ≫ β.hom.app (op (s.obj U)) := by
  have he := congrArg (fun k => k.hom.app (op U)) h
  have hd := congrArg (fun k => (k.app H).hom.app (op U)) hδ
  change uX.hom.app (op (r.obj U)) ≫ (δ.app H).hom.app (op U) =
    uS.hom.app (op U) ≫ β.hom.app (op (s.obj U)) at he
  change (δ.app H).hom.app (op U) = H.obj.map (σ.app U).op at hd
  exact (congrArg (fun k => uX.hom.app (op (r.obj U)) ≫ k) hd).symm.trans he

namespace AlgebraicGeometry.Scheme.EtaleCohomology.SmoothBaseChange
open Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- An arbitrary original unit representative is invertible when its actual
relative projection has the connected pullback hypotheses. -/
theorem unitSectionMap_isIso_of_connected_projection
    {X S : Scheme.{u}} (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    {U : X.Etale} {T : S.Etale} (a : T ⟶ (siteBaseChange f).obj U)
    [QuasiCompact (unitRepresentativeArrow f a).left]
    [QuasiSeparated (unitRepresentativeArrow f a).left]
    [GeometricallyConnected (unitRepresentativeArrow f a).left]
    [UniversallyOpen (unitRepresentativeArrow f a).left]
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) :
    IsIso (unitSectionMap f F a) := by
  let b := (unitRepresentativeArrow f a).left
  let p := Functor.whiskerLeft (inverseImage U.hom) (globalSectionsPullbackNatTrans b)
  let : IsIso (p.app F) :=
    globalSectionsPullback_isIso_of_geometricallyConnected b ((inverseImage U.hom).obj F)
      n hn (inverseImage_nsmul_id_eq_zero_of_killed U.hom F n hF)
  exact unitComponent_isIso_of_whole_square
    (unitSectionNatTrans f a)
    (pullbackSectionsEtaleEvaluationNatIso U).symm
    (Functor.isoWhiskerLeft (inverseImage f) (pullbackSectionsEtaleEvaluationNatIso T).symm)
    p (Functor.isoWhiskerRight
      (inverseImageSquareIso U.hom T.hom f b (Over.w (unitRepresentativeArrow f a)).symm).symm
      (globalSections T.left))
    (unitSectionNatTrans_square f a) F

/-- The actual horizontal unit equation at an original base chart, retaining
the literal site-square arrow and the literal ordinary exchange component. -/
private theorem ordinaryChart_horizontalUnit_component
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (F : AbelianSheaf.{u, u + 1} X) (V : S.Etale) :
    ((inverseImageAdjunction (pullback.snd g f)).unit.app F).hom.app
        (op ((siteBaseChange f).obj V)) ≫
      ((inverseImage (pullback.snd g f)).obj F).obj.map
        ((siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
          pullback.condition).hom.app V).op =
    ((inverseImageAdjunction g).unit.app ((directImage f).obj F)).hom.app (op V) ≫
      ((baseChangeMap f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition).app F).hom.app (op ((siteBaseChange g).obj V)) := by
  let : (siteBaseChange g ⋙ siteBaseChange (pullback.fst g f)).IsContinuous
      S.smallEtaleTopology (pullback g f).smallEtaleTopology :=
    Functor.isContinuous_comp (siteBaseChange g) (siteBaseChange (pullback.fst g f))
      S.smallEtaleTopology S'.smallEtaleTopology (pullback g f).smallEtaleTopology
  let : (siteBaseChange f ⋙ siteBaseChange (pullback.snd g f)).IsContinuous
      S.smallEtaleTopology (pullback g f).smallEtaleTopology :=
    Functor.isContinuous_comp (siteBaseChange f) (siteBaseChange (pullback.snd g f))
      S.smallEtaleTopology X.smallEtaleTopology (pullback g f).smallEtaleTopology
  exact originalContinuousSquare_unit_evaluation
    S.smallEtaleTopology X.smallEtaleTopology S'.smallEtaleTopology
    (pullback g f).smallEtaleTopology
    (siteBaseChange f) (siteBaseChange g)
    (siteBaseChange (pullback.snd g f)) (siteBaseChange (pullback.fst g f))
    (siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).hom
    (directImageSquareIso f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).hom
    (directImageSquareIso_transform f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition)
    F ((inverseImage g).obj ((directImage f).obj F))
    ((inverseImage (pullback.snd g f)).obj F)
    ((inverseImageAdjunction (pullback.snd g f)).unit.app F)
    ((inverseImageAdjunction g).unit.app ((directImage f).obj F))
    ((baseChangeMap f (pullback.fst g f) g (pullback.snd g f) pullback.condition).app F)
    (baseChangeMap_horizontal_unit f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition F) V

/-- The canonical ordinary mate is invertible on the given original test,
when its actual representative projection is qcqs, open and geometrically
connected. The total-space hypotheses follow from the original cartesian law. -/
theorem ordinaryChart_component_isIso
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (F : AbelianSheaf.{u, u + 1} X) {V : S.Etale} {T : S'.Etale}
    (a : T ⟶ (siteBaseChange g).obj V)
    [QuasiCompact (unitRepresentativeArrow g a).left]
    [QuasiSeparated (unitRepresentativeArrow g a).left]
    [GeometricallyConnected (unitRepresentativeArrow g a).left]
    [UniversallyOpen (unitRepresentativeArrow g a).left]
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) :
    IsIso (((baseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).app F).hom.app (op T)) := by
  let aX := ordinaryChartTotalTest f g a
  have hs := ordinaryChartTotalTest_isPullback f g a
  let : QuasiCompact (unitRepresentativeArrow (pullback.snd g f) aX).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hs.flip inferInstance
  let : QuasiSeparated (unitRepresentativeArrow (pullback.snd g f) aX).left :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) hs.flip inferInstance
  let : GeometricallyConnected (unitRepresentativeArrow (pullback.snd g f) aX).left :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hs.flip inferInstance
  let : UniversallyOpen (unitRepresentativeArrow (pullback.snd g f) aX).left :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen) hs.flip inferInstance
  let hu : IsIso
      (((inverseImageAdjunction g).unit.app ((directImage f).obj F)).hom.app (op V) ≫
        ((inverseImage g).obj ((directImage f).obj F)).obj.map a.op) :=
    show IsIso (unitSectionMap g ((directImage f).obj F) a) from
      unitSectionMap_isIso_of_connected_projection g ((directImage f).obj F) a n hn
        (directImage_nsmul_id_eq_zero_of_killed f F n hF)
  let hv : IsIso
      (((inverseImageAdjunction (pullback.snd g f)).unit.app F).hom.app
          (op ((siteBaseChange f).obj V)) ≫
        ((inverseImage (pullback.snd g f)).obj F).obj.map
          ((siteBaseChange (pullback.fst g f)).map a ≫
            (siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
              pullback.condition).hom.app V).op) :=
    show IsIso (unitSectionMap (pullback.snd g f) F aX) from
      unitSectionMap_isIso_of_connected_projection (pullback.snd g f) F aX n hn hF
  exact originalMate_component_isIso_of_units (hu := hu) (hv := hv)
    (siteBaseChange (pullback.fst g f))
    (((inverseImage g).obj ((directImage f).obj F)).obj)
    (((inverseImage (pullback.snd g f)).obj F).obj)
    ((baseChangeMap f (pullback.fst g f) g (pullback.snd g f) pullback.condition).app F).hom
    a ((siteBaseChangeSquareIso f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).hom.app V)
    (((inverseImageAdjunction g).unit.app ((directImage f).obj F)).hom.app (op V))
    (((inverseImageAdjunction (pullback.snd g f)).unit.app F).hom.app
      (op ((siteBaseChange f).obj V)))
    (ordinaryChart_horizontalUnit_component f g F V)

end AlgebraicGeometry.Scheme.EtaleCohomology.SmoothBaseChange
