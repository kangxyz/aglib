/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.OrdinaryConnectedCharts

/-! # Original section exchange for an etale-connected tower

The original horizontal unit equation and presheaf naturality determine the
literal ordinary exchange on the terminal test. Its base representative is
the original connected projection, and its total representative is its actual
base change. No local factorization for an arbitrary smooth morphism or
comparison with a replacement exchange is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Continuity SmoothBaseChange

universe u

attribute [local instance] hasSheafifyLarge

/-- The original site square transports the same test on an actual square. -/
private def actualSquareTotalTest
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : f' ≫ g = g' ≫ f)
    {V : S.Etale} {T : S'.Etale} (a : T ⟶ (siteBaseChange g).obj V) :
    (siteBaseChange f').obj T ⟶ (siteBaseChange g').obj ((siteBaseChange f).obj V) :=
  (siteBaseChange f').map a ≫ (siteBaseChangeSquareIso f f' g g' h).hom.app V

/-- The original total representative preserves the original base representative. -/
private theorem actualSquareTotalTest_fst
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : f' ≫ g = g' ≫ f)
    {V : S.Etale} {T : S'.Etale} (a : T ⟶ (siteBaseChange g).obj V) :
    (unitRepresentativeArrow g' (actualSquareTotalTest f f' g g' h a)).left ≫
        pullback.fst V.hom f =
      pullback.fst T.hom f' ≫ (unitRepresentativeArrow g a).left := by
  let m := ((siteBaseChange f').map a).left
  let i := ((siteBaseChangeSquareIso f f' g g' h).hom.app V).left
  have hi := siteBaseChangeSquareIso_fst_fst f f' g g' h V
  have hm := siteBaseChange_map_fst f' a
  change ((m ≫ i) ≫ pullback.fst (pullback.snd V.hom f) g') ≫
      pullback.fst V.hom f = pullback.fst T.hom f' ≫ a.left ≫ pullback.fst V.hom g
  have h₁ :=
    (Category.assoc (m ≫ i) (pullback.fst (pullback.snd V.hom f) g')
      (pullback.fst V.hom f)).trans
        (Category.assoc m i (pullback.fst (pullback.snd V.hom f) g' ≫
          pullback.fst V.hom f))
  have h₂ := congrArg (fun k => m ≫ k) hi
  have h₃ :=
    (Category.assoc m (pullback.fst (pullback.snd V.hom g) f')
      (pullback.fst V.hom g)).symm.trans
        ((congrArg (fun k => k ≫ pullback.fst V.hom g) hm).trans
          (Category.assoc (pullback.fst T.hom f') a.left (pullback.fst V.hom g)))
  exact h₁.trans (h₂.trans h₃)

/-- The total representative retains the literal total-space structural arrow. -/
private theorem actualSquareTotalTest_snd
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : f' ≫ g = g' ≫ f)
    {V : S.Etale} {T : S'.Etale} (a : T ⟶ (siteBaseChange g).obj V) :
    (unitRepresentativeArrow g' (actualSquareTotalTest f f' g g' h a)).left ≫
        pullback.snd V.hom f = pullback.snd T.hom f' ≫ g' :=
  Over.w (unitRepresentativeArrow g' (actualSquareTotalTest f f' g g' h a))

/-- On the original Cartesian square, the two actual representatives are Cartesian. -/
private theorem actualSquareTotalTest_isPullback
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : f' ≫ g = g' ≫ f)
    (H : IsPullback g' f' f g)
    {V : S.Etale} {T : S'.Etale} (a : T ⟶ (siteBaseChange g).obj V) :
    IsPullback
      (unitRepresentativeArrow g' (actualSquareTotalTest f f' g g' h a)).left
      (pullback.fst T.hom f') (pullback.fst V.hom f)
      (unitRepresentativeArrow g a).left := by
  have H₀ : IsPullback (pullback.snd T.hom f' ≫ g')
      (pullback.fst T.hom f') f (T.hom ≫ g) :=
    (IsPullback.of_hasPullback T.hom f').flip.paste_horiz H
  have hp : (unitRepresentativeArrow g a).left ≫ V.hom = T.hom ≫ g :=
    Over.w (unitRepresentativeArrow g a)
  have H₁ : IsPullback
      ((unitRepresentativeArrow g' (actualSquareTotalTest f f' g g' h a)).left ≫
        pullback.snd V.hom f)
      (pullback.fst T.hom f') f ((unitRepresentativeArrow g a).left ≫ V.hom) := by
    rw [actualSquareTotalTest_snd, hp]
    exact H₀
  exact H₁.of_right (actualSquareTotalTest_fst f f' g g' h a)
    (IsPullback.of_hasPullback V.hom f).flip

/-- Evaluate the original whole horizontal unit on the original base test. -/
private theorem actualSquare_horizontalUnit_component
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : f' ≫ g = g' ≫ f)
    (F : AbelianSheaf.{u, u + 1} X) (V : S.Etale) :
    ((inverseImageAdjunction g').unit.app F).hom.app (op ((siteBaseChange f).obj V)) ≫
      ((inverseImage g').obj F).obj.map
        ((siteBaseChangeSquareIso f f' g g' h).hom.app V).op =
      ((inverseImageAdjunction g).unit.app ((directImage f).obj F)).hom.app (op V) ≫
        ((baseChangeMap f f' g g' h).app F).hom.app (op ((siteBaseChange g).obj V)) := by
  let : (siteBaseChange g ⋙ siteBaseChange f').IsContinuous
      S.smallEtaleTopology X'.smallEtaleTopology :=
    Functor.isContinuous_comp (siteBaseChange g) (siteBaseChange f')
      S.smallEtaleTopology S'.smallEtaleTopology X'.smallEtaleTopology
  let : (siteBaseChange f ⋙ siteBaseChange g').IsContinuous
      S.smallEtaleTopology X'.smallEtaleTopology :=
    Functor.isContinuous_comp (siteBaseChange f) (siteBaseChange g')
      S.smallEtaleTopology X.smallEtaleTopology X'.smallEtaleTopology
  exact originalContinuousSquare_unit_evaluation
    S.smallEtaleTopology X.smallEtaleTopology S'.smallEtaleTopology X'.smallEtaleTopology
    (siteBaseChange f) (siteBaseChange g) (siteBaseChange g') (siteBaseChange f')
    (siteBaseChangeSquareIso f f' g g' h).hom
    (directImageSquareIso f f' g g' h).hom
    (directImageSquareIso_transform f f' g g' h)
    F ((inverseImage g).obj ((directImage f).obj F)) ((inverseImage g').obj F)
    ((inverseImageAdjunction g').unit.app F)
    ((inverseImageAdjunction g).unit.app ((directImage f).obj F))
    ((baseChangeMap f f' g g' h).app F)
    (baseChangeMap_horizontal_unit f f' g g' h F) V

/-- The actual twice-pulled-back square has the literal composite triangle. -/
theorem connectedEtaleTower_comm
    {X S V W : Scheme.{u}} (f : X ⟶ S) (e : V ⟶ S) (p : W ⟶ V) :
    pullback.fst p (pullback.fst e f) ≫ (p ≫ e) =
      (pullback.snd p (pullback.fst e f) ≫ pullback.snd e f) ≫ f := by
  rw [← Category.assoc, pullback.condition, Category.assoc,
    pullback.condition, ← Category.assoc]

/-- The literal overall ordinary exchange on an actual etale-connected tower
is invertible on original global sections. This does not construct a local
factorization or assert that the exchange is an isomorphism of sheaves. -/
theorem baseChangeMap_globalSections_isIso_of_etale_connected_tower
    {X S V W : Scheme.{u}} (f : X ⟶ S) (e : V ⟶ S) (p : W ⟶ V)
    [Etale e] [QuasiCompact p] [QuasiSeparated p]
    [GeometricallyConnected p] [UniversallyOpen p]
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) :
    IsIso ((globalSections W).map
      ((baseChangeMap f (pullback.fst p (pullback.fst e f)) (p ≫ e)
        (pullback.snd p (pullback.fst e f) ≫ pullback.snd e f)
        (connectedEtaleTower_comm f e p)).app F)) := by
  have hpQc : QuasiCompact p := inferInstance
  have hpQs : QuasiSeparated p := inferInstance
  have hpGc : GeometricallyConnected p := inferInstance
  have hpOpen : UniversallyOpen p := inferInstance
  let f₁ := pullback.fst e f
  let f₂ := pullback.fst p f₁
  let h₁ := pullback.snd e f
  let h₂ := pullback.snd p f₁
  let g := p ≫ e
  let g' := h₂ ≫ h₁
  let h := connectedEtaleTower_comm f e p
  let H : IsPullback g' f₂ f g :=
    (IsPullback.of_hasPullback p f₁).flip.paste_horiz
      (IsPullback.of_hasPullback e f).flip
  let U : S.Etale := Scheme.Etale.mk e
  let a := relativeTerminalTest g U p rfl
  have ha : (unitRepresentativeArrow g a).left = p := pullback.lift_fst _ _ _
  let : QuasiCompact (unitRepresentativeArrow g a).left :=
    Eq.mpr (congrArg (fun b : W ⟶ V => QuasiCompact b) ha) hpQc
  let : QuasiSeparated (unitRepresentativeArrow g a).left :=
    Eq.mpr (congrArg (fun b : W ⟶ V => QuasiSeparated b) ha) hpQs
  let : GeometricallyConnected (unitRepresentativeArrow g a).left :=
    Eq.mpr (congrArg (fun b : W ⟶ V => GeometricallyConnected b) ha) hpGc
  let : UniversallyOpen (unitRepresentativeArrow g a).left :=
    Eq.mpr (congrArg (fun b : W ⟶ V => UniversallyOpen b) ha) hpOpen
  let aX := actualSquareTotalTest f f₂ g g' h a
  have hs := actualSquareTotalTest_isPullback f f₂ g g' h H a
  let : QuasiCompact (unitRepresentativeArrow g' aX).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hs.flip inferInstance
  let : QuasiSeparated (unitRepresentativeArrow g' aX).left :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) hs.flip inferInstance
  let : GeometricallyConnected (unitRepresentativeArrow g' aX).left :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hs.flip inferInstance
  let : UniversallyOpen (unitRepresentativeArrow g' aX).left :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen) hs.flip inferInstance
  let hu : IsIso
      (((inverseImageAdjunction g).unit.app ((directImage f).obj F)).hom.app (op U) ≫
        ((inverseImage g).obj ((directImage f).obj F)).obj.map a.op) :=
    show IsIso (unitSectionMap g ((directImage f).obj F) a) from
      unitSectionMap_isIso_of_connected_projection g ((directImage f).obj F) a n hn
        (directImage_nsmul_id_eq_zero_of_killed f F n hF)
  let hv : IsIso
      (((inverseImageAdjunction g').unit.app F).hom.app (op ((siteBaseChange f).obj U)) ≫
        ((inverseImage g').obj F).obj.map
          ((siteBaseChange f₂).map a ≫
            (siteBaseChangeSquareIso f f₂ g g' h).hom.app U).op) :=
    show IsIso (unitSectionMap g' F aX) from
      unitSectionMap_isIso_of_connected_projection g' F aX n hn hF
  exact originalMate_component_isIso_of_units (hu := hu) (hv := hv)
    (siteBaseChange f₂)
    (((inverseImage g).obj ((directImage f).obj F)).obj)
    (((inverseImage g').obj F).obj)
    ((baseChangeMap f f₂ g g' h).app F).hom
    a ((siteBaseChangeSquareIso f f₂ g g' h).hom.app U)
    (((inverseImageAdjunction g).unit.app ((directImage f).obj F)).hom.app (op U))
    (((inverseImageAdjunction g').unit.app F).hom.app (op ((siteBaseChange f).obj U)))
    (actualSquare_horizontalUnit_component f f₂ g g' h F U)

end AlgebraicGeometry.Scheme.EtaleCohomology
