/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # The actual Over chart-tail family and its oriented cone

The native post/pullback/map recipe defines one family over the original base.
Its chosen cone, chart-variable naturality, pullback-symmetry comparison and
identity-chart normalization use the same selected pullbacks throughout.
Only the native conePost limit step requires a cofiltered index category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Over.ChartTails

universe uC vC uI vI

variable {C : Type uC} [Category.{vC} C] [HasPullbacks C]
  {I : Type uI} [Category.{vI} I] {X : C}

/-- Actual pullbacks of a stage chart, still over the original base object. -/
def chartTail (D : I ⥤ Over X) (i : I) (U : Over (D.obj i).left) :
    Over i ⥤ Over X :=
  Over.post (D ⋙ Over.forget X) ⋙ Over.pullback U.hom ⋙ Over.map (U.hom ≫ (D.obj i).hom)

/-- The original limit cone base-changed to a stage chart and retained over the base. -/
def chartTailCone (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : Over (D.obj i).left) : Cone (chartTail D i U) :=
  (Over.pullback U.hom ⋙ Over.map (U.hom ≫ (D.obj i).hom)).mapCone
    ((Over.conePost (D ⋙ Over.forget X) i).obj ((Over.forget X).mapCone c))

/-- The supplied underlying limit remains the actual chart-tail limit. -/
def chartTailConeIsLimit [IsCofiltered I]
    (D : I ⥤ Over X) (c : Cone D) (hc : IsLimit ((Over.forget X).mapCone c))
    (i : I) (U : Over (D.obj i).left) :
    IsLimit ((Over.forget X).mapCone (chartTailCone D c i U)) := by
  change IsLimit ((Over.pullback U.hom ⋙ Over.forget U.left).mapCone
    ((Over.conePost (D ⋙ Over.forget X) i).obj ((Over.forget X).mapCone c)))
  letI : IsConnected (Over i) := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.pullback U.hom ⋙ Over.forget U.left)
    (Over.isLimitConePost i hc)

/-- The native chart-tail projection has the original first pullback projection. -/
theorem chartTailCone_π_fst (D : I ⥤ Over X) (c : Cone D)
    (i : I) (U : Over (D.obj i).left) (j : Over i) :
    ((chartTailCone D c i U).π.app j).left ≫
        Limits.pullback.fst (D.map j.hom).left U.hom =
      Limits.pullback.fst (c.π.app i).left U.hom ≫ (c.π.app j.left).left := by
  change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _ = _
  exact Limits.pullback.lift_fst _ _ _

/-- The native chart-tail projection preserves the original chart coordinate. -/
theorem chartTailCone_π_snd (D : I ⥤ Over X) (c : Cone D)
    (i : I) (U : Over (D.obj i).left) (j : Over i) :
    ((chartTailCone D c i U).π.app j).left ≫
        Limits.pullback.snd (D.map j.hom).left U.hom =
      Limits.pullback.snd (c.π.app i).left U.hom := by
  change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = _
  exact Limits.pullback.lift_snd _ _ _

/-- The original tail arrow preserves the stage coordinate. -/
@[reassoc]
theorem chartTail_map_fst (D : I ⥤ Over X) (i : I)
    (U : Over (D.obj i).left) {j k : Over i} (a : j ⟶ k) :
    ((chartTail D i U).map a).left ≫ Limits.pullback.fst (D.map k.hom).left U.hom =
      Limits.pullback.fst (D.map j.hom).left U.hom ≫ (D.map a.left).left := by
  change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _ = _
  exact Limits.pullback.lift_fst _ _ _

/-- The original tail arrow preserves the chart coordinate. -/
@[reassoc]
theorem chartTail_map_snd (D : I ⥤ Over X) (i : I)
    (U : Over (D.obj i).left) {j k : Over i} (a : j ⟶ k) :
    ((chartTail D i U).map a).left ≫ Limits.pullback.snd (D.map k.hom).left U.hom =
      Limits.pullback.snd (D.map j.hom).left U.hom := by
  change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = _
  exact Limits.pullback.lift_snd _ _ _

/-- An original chart morphism gives its actual stage pullback map over the base. -/
def chartTailMapApp (D : I ⥤ Over X) (i : I)
    {U V : Over (D.obj i).left} (a : U ⟶ V) (j : Over i) :
    (chartTail D i U).obj j ⟶ (chartTail D i V).obj j :=
  Over.homMk (Limits.pullback.lift (Limits.pullback.fst (D.map j.hom).left U.hom)
    (Limits.pullback.snd (D.map j.hom).left U.hom ≫ a.left) (by
      have hw : a.left ≫ V.hom = U.hom := Over.w a
      exact Limits.pullback.condition.trans ((Category.assoc _ _ _).trans
        (congrArg (fun z ↦ Limits.pullback.snd (D.map j.hom).left U.hom ≫ z) hw)).symm)) (by
    change (Limits.pullback.lift _ _ _) ≫ (Limits.pullback.snd (D.map j.hom).left V.hom ≫
      V.hom ≫ (D.obj i).hom) = Limits.pullback.snd (D.map j.hom).left U.hom ≫ U.hom ≫ (D.obj i).hom
    have hw : a.left ≫ V.hom = U.hom := Over.w a
    exact (Limits.pullback.lift_snd_assoc _ _ _ _).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z ↦ Limits.pullback.snd (D.map j.hom).left U.hom ≫ z)
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun z ↦ z ≫ (D.obj i).hom) hw)))))

@[reassoc]
theorem chartTailMapApp_fst (D : I ⥤ Over X) (i : I)
    {U V : Over (D.obj i).left} (a : U ⟶ V) (j : Over i) :
    (chartTailMapApp D i a j).left ≫ Limits.pullback.fst (D.map j.hom).left V.hom =
      Limits.pullback.fst (D.map j.hom).left U.hom := by
  exact Limits.pullback.lift_fst _ _ _

@[reassoc]
theorem chartTailMapApp_snd (D : I ⥤ Over X) (i : I)
    {U V : Over (D.obj i).left} (a : U ⟶ V) (j : Over i) :
    (chartTailMapApp D i a j).left ≫ Limits.pullback.snd (D.map j.hom).left V.hom =
      Limits.pullback.snd (D.map j.hom).left U.hom ≫ a.left := by
  exact Limits.pullback.lift_snd _ _ _

/-- Chart morphisms act naturally on actual relative chart tails. -/
def chartTailMap (D : I ⥤ Over X) (i : I)
    {U V : Over (D.obj i).left} (a : U ⟶ V) :
    chartTail D i U ⟶ chartTail D i V where
  app := chartTailMapApp D i a
  naturality {j k} b := by
    apply Over.OverMorphism.ext
    apply Limits.pullback.hom_ext
    · have hleft := (Category.assoc
        ((chartTail D i U).map b).left
        (chartTailMapApp D i a k).left
        (Limits.pullback.fst (D.map k.hom).left V.hom)).trans
          ((congrArg (fun z ↦ ((chartTail D i U).map b).left ≫ z)
            (chartTailMapApp_fst D i a k)).trans
              (chartTail_map_fst D i U b))
      have hright := (Category.assoc
        (chartTailMapApp D i a j).left
        ((chartTail D i V).map b).left
        (Limits.pullback.fst (D.map k.hom).left V.hom)).trans
          ((congrArg (fun z ↦ (chartTailMapApp D i a j).left ≫ z)
            (chartTail_map_fst D i V b)).trans
              ((Category.assoc _ _ _).symm.trans
                (congrArg (fun z ↦ z ≫ (D.map b.left).left)
                  (chartTailMapApp_fst D i a j))))
      exact hleft.trans hright.symm
    · have hleft := (Category.assoc
        ((chartTail D i U).map b).left
        (chartTailMapApp D i a k).left
        (Limits.pullback.snd (D.map k.hom).left V.hom)).trans
          ((congrArg (fun z ↦ ((chartTail D i U).map b).left ≫ z)
            (chartTailMapApp_snd D i a k)).trans
              ((Category.assoc _ _ _).symm.trans
                (congrArg (fun z ↦ z ≫ a.left) (chartTail_map_snd D i U b))))
      have hright := (Category.assoc
        (chartTailMapApp D i a j).left
        ((chartTail D i V).map b).left
        (Limits.pullback.snd (D.map k.hom).left V.hom)).trans
          ((congrArg (fun z ↦ (chartTailMapApp D i a j).left ≫ z)
            (chartTail_map_snd D i V b)).trans
              (chartTailMapApp_snd D i a j))
      exact hleft.trans hright.symm

/-- The actual Over chart category acts functorially on its relative tails. -/
def chartTails (D : I ⥤ Over X) (i : I) :
    Over (D.obj i).left ⥤ (Over i ⥤ Over X) where
  obj := chartTail D i
  map := chartTailMap D i
  map_id U := by
    apply NatTrans.ext
    funext j
    apply Over.OverMorphism.ext
    change (chartTailMapApp D i (𝟙 U) j).left = 𝟙 _
    apply Limits.pullback.hom_ext
    · exact (chartTailMapApp_fst D i (𝟙 U) j).trans (Category.id_comp _).symm
    · have hid : (show U ⟶ U from 𝟙 U).left = 𝟙 U.left := rfl
      exact (chartTailMapApp_snd D i (𝟙 U) j).trans
        ((congrArg (fun z ↦ Limits.pullback.snd (D.map j.hom).left U.hom ≫ z) hid).trans
          ((Category.comp_id _).trans (Category.id_comp _).symm))
  map_comp a b := by
    apply NatTrans.ext
    funext j
    apply Over.OverMorphism.ext
    change (chartTailMapApp D i (a ≫ b) j).left =
      (chartTailMapApp D i a j).left ≫ (chartTailMapApp D i b j).left
    apply Limits.pullback.hom_ext
    · exact (chartTailMapApp_fst D i (a ≫ b) j).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ (chartTailMapApp D i a j).left ≫ z)
            (chartTailMapApp_fst D i b j)).trans
              (chartTailMapApp_fst D i a j))).symm
    · have hab : (a ≫ b).left = a.left ≫ b.left := rfl
      have hleft := (chartTailMapApp_snd D i (a ≫ b) j).trans
        (congrArg (fun z ↦ Limits.pullback.snd (D.map j.hom).left _ ≫ z) hab)
      have hright := (Category.assoc
        (chartTailMapApp D i a j).left (chartTailMapApp D i b j).left
        (Limits.pullback.snd (D.map j.hom).left _)).trans
          ((congrArg (fun z ↦ (chartTailMapApp D i a j).left ≫ z)
            (chartTailMapApp_snd D i b j)).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (fun z ↦ z ≫ b.left) (chartTailMapApp_snd D i a j)).trans
                  (Category.assoc _ _ _))))
      exact hleft.trans hright.symm

/-- The native Over pullback map preserves the original source coordinate. -/
@[reassoc]
theorem chartPullback_map_fst {Y Z : C} (f : Y ⟶ Z)
    {U V : Over Z} (a : U ⟶ V) :
    ((Over.pullback f).map a).left ≫ Limits.pullback.fst V.hom f =
      Limits.pullback.fst U.hom f ≫ a.left := by
  exact Limits.pullback.lift_fst _ _ _

/-- The native Over pullback map preserves the base coordinate. -/
@[reassoc]
theorem chartPullback_map_snd {Y Z : C} (f : Y ⟶ Z)
    {U V : Over Z} (a : U ⟶ V) :
    ((Over.pullback f).map a).left ≫ Limits.pullback.snd V.hom f =
      Limits.pullback.snd U.hom f := by
  exact Limits.pullback.lift_snd _ _ _

/-- Original base change of charts to the supplied limit, retained over X. -/
def nativeLimitChartFunctor (D : I ⥤ Over X) (c : Cone D) (i : I) :
    Over (D.obj i).left ⥤ Over X :=
  Over.pullback (c.π.app i).left ⋙ Over.map c.pt.hom

/-- The original pullback orientation is identified with the actual tail limit. -/
def nativeLimitChartIso (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : Over (D.obj i).left) :
    (nativeLimitChartFunctor D c i).obj U ≅ (chartTailCone D c i U).pt :=
  Over.isoMk (pullbackSymmetry U.hom (c.π.app i).left) (by
    change (pullbackSymmetry U.hom (c.π.app i).left).hom ≫
      (Limits.pullback.snd (c.π.app i).left U.hom ≫ U.hom ≫ (D.obj i).hom) =
      Limits.pullback.snd U.hom (c.π.app i).left ≫ c.pt.hom
    exact (pullbackSymmetry_hom_comp_snd_assoc _ _ _).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ (D.obj i).hom) Limits.pullback.condition).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ Limits.pullback.snd U.hom (c.π.app i).left ≫ z)
            (Over.w (c.π.app i)))))))

/-- Actual chart-tail cone with the original pullback object as its point. -/
def nativeChartTailCone (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : Over (D.obj i).left) : Cone (chartTail D i U) :=
  (chartTailCone D c i U).extend (nativeLimitChartIso D c i U).hom

@[reassoc]
theorem nativeChartTailCone_π_fst (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : Over (D.obj i).left) (j : Over i) :
    ((nativeChartTailCone D c i U).π.app j).left ≫
      Limits.pullback.fst (D.map j.hom).left U.hom =
      Limits.pullback.snd U.hom (c.π.app i).left ≫ (c.π.app j.left).left := by
  change ((pullbackSymmetry U.hom (c.π.app i).left).hom ≫
    ((chartTailCone D c i U).π.app j).left) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ (pullbackSymmetry U.hom (c.π.app i).left).hom ≫ z)
      (chartTailCone_π_fst D c i U j)).trans
      (pullbackSymmetry_hom_comp_fst_assoc _ _ _))

@[reassoc]
theorem nativeChartTailCone_π_snd (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : Over (D.obj i).left) (j : Over i) :
    ((nativeChartTailCone D c i U).π.app j).left ≫
      Limits.pullback.snd (D.map j.hom).left U.hom =
        Limits.pullback.fst U.hom (c.π.app i).left := by
  change ((pullbackSymmetry U.hom (c.π.app i).left).hom ≫
    ((chartTailCone D c i U).π.app j).left) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ (pullbackSymmetry U.hom (c.π.app i).left).hom ≫ z)
      (chartTailCone_π_snd D c i U j)).trans
      (pullbackSymmetry_hom_comp_snd _ _))

/-- The original oriented cone retains the actual underlying limit. -/
def nativeChartTailConeIsLimit [IsCofiltered I] (D : I ⥤ Over X) (c : Cone D)
    (hc : IsLimit ((Over.forget X).mapCone c)) (i : I) (U : Over (D.obj i).left) :
    IsLimit ((Over.forget X).mapCone (nativeChartTailCone D c i U)) := by
  let e := (Over.forget X).mapIso (nativeLimitChartIso D c i U)
  exact (chartTailConeIsLimit D c hc i U).ofIsoLimit
    (Cone.extendIso ((Over.forget X).mapCone (chartTailCone D c i U)) e.symm)

/-- The cone leg is natural in the original chart variable. -/
def nativeChartTailLeg (D : I ⥤ Over X) (c : Cone D) (i : I) (j : Over i) :
    nativeLimitChartFunctor D c i ⟶ (chartTails D i).flip.obj j where
  app U := (nativeChartTailCone D c i U).π.app j
  naturality {U V} a := by
    apply Over.OverMorphism.ext
    apply Limits.pullback.hom_ext
    · change (((Over.pullback (c.π.app i).left).map a).left ≫
        ((nativeChartTailCone D c i V).π.app j).left) ≫ _ =
        (((nativeChartTailCone D c i U).π.app j).left ≫
          (chartTailMapApp D i a j).left) ≫ _
      exact ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ ((Over.pullback (c.π.app i).left).map a).left ≫ z)
          (nativeChartTailCone_π_fst D c i V j)).trans
          (chartPullback_map_snd_assoc (c.π.app i).left a _))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ ((nativeChartTailCone D c i U).π.app j).left ≫ z)
            (chartTailMapApp_fst D i a j)).trans
            (nativeChartTailCone_π_fst D c i U j))).symm
    · change (((Over.pullback (c.π.app i).left).map a).left ≫
        ((nativeChartTailCone D c i V).π.app j).left) ≫ _ =
        (((nativeChartTailCone D c i U).π.app j).left ≫
          (chartTailMapApp D i a j).left) ≫ _
      exact ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ ((Over.pullback (c.π.app i).left).map a).left ≫ z)
          (nativeChartTailCone_π_snd D c i V j)).trans
          (chartPullback_map_fst (c.π.app i).left a))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ ((nativeChartTailCone D c i U).π.app j).left ≫ z)
            (chartTailMapApp_snd D i a j)).trans
            ((Category.assoc _ _ _).symm.trans
              (nativeChartTailCone_π_snd_assoc D c i U j a.left)))).symm

/-- One cone in the chart-functor category, not unrelated objectwise choices. -/
def nativeChartTailsCone (D : I ⥤ Over X) (c : Cone D) (i : I) :
    Cone (chartTails D i).flip where
  pt := nativeLimitChartFunctor D c i
  π :=
    { app := nativeChartTailLeg D c i
      naturality {j k} a := by
        apply NatTrans.ext
        funext U
        change (𝟙 _) ≫ (nativeChartTailCone D c i U).π.app k =
          (nativeChartTailCone D c i U).π.app j ≫ (chartTail D i U).map a
        exact (Category.id_comp _).trans ((nativeChartTailCone D c i U).w a).symm }

/-- Original stage pullback, retained over the coefficient base. -/
def nativeStageChartFunctor (D : I ⥤ Over X) (i : I) (j : Over i) :
    Over (D.obj i).left ⥤ Over X :=
  Over.pullback (D.map j.hom).left ⋙
    Over.map (D.obj j.left).hom

/-- The stage comparison keeps the actual pullback-symmetry map. -/
def nativeStageChartIso (D : I ⥤ Over X) (i : I) (j : Over i)
    (U : Over (D.obj i).left) :
    (nativeStageChartFunctor D i j).obj U ≅ (chartTail D i U).obj j :=
  Over.isoMk (pullbackSymmetry U.hom (D.map j.hom).left) (by
    change (pullbackSymmetry U.hom (D.map j.hom).left).hom ≫
      (Limits.pullback.snd (D.map j.hom).left U.hom ≫ U.hom ≫ (D.obj i).hom) =
      Limits.pullback.snd U.hom (D.map j.hom).left ≫ (D.obj j.left).hom
    exact (pullbackSymmetry_hom_comp_snd_assoc _ _ _).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ (D.obj i).hom) Limits.pullback.condition).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ Limits.pullback.snd U.hom (D.map j.hom).left ≫ z)
            (Over.w (D.map j.hom)))))))

/-- The actual stage-orientation comparison is natural in the original chart. -/
def nativeStageChartsIso (D : I ⥤ Over X) (i : I) (j : Over i) :
    nativeStageChartFunctor D i j ≅ (chartTails D i).flip.obj j :=
  NatIso.ofComponents (nativeStageChartIso D i j) (by
    intro U V a
    apply Over.OverMorphism.ext
    apply Limits.pullback.hom_ext
    · change (((Over.pullback (D.map j.hom).left).map a).left ≫
        (pullbackSymmetry V.hom (D.map j.hom).left).hom) ≫ _ =
        ((pullbackSymmetry U.hom (D.map j.hom).left).hom ≫
          (chartTailMapApp D i a j).left) ≫ _
      exact ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ ((Over.pullback (D.map j.hom).left).map a).left ≫ z)
          (pullbackSymmetry_hom_comp_fst V.hom (D.map j.hom).left)).trans
          (chartPullback_map_snd (D.map j.hom).left a))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ (pullbackSymmetry U.hom (D.map j.hom).left).hom ≫ z)
            (chartTailMapApp_fst D i a j)).trans
            (pullbackSymmetry_hom_comp_fst _ _))).symm
    · change (((Over.pullback (D.map j.hom).left).map a).left ≫
        (pullbackSymmetry V.hom (D.map j.hom).left).hom) ≫ _ =
        ((pullbackSymmetry U.hom (D.map j.hom).left).hom ≫
          (chartTailMapApp D i a j).left) ≫ _
      exact ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ ((Over.pullback (D.map j.hom).left).map a).left ≫ z)
          (pullbackSymmetry_hom_comp_snd V.hom (D.map j.hom).left)).trans
          (chartPullback_map_fst (D.map j.hom).left a))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ (pullbackSymmetry U.hom (D.map j.hom).left).hom ≫ z)
            (chartTailMapApp_snd D i a j)).trans
            (pullbackSymmetry_hom_comp_snd_assoc _ _ a.left))).symm)

/-- At the terminal chart the actual tail recovers the original stage-tail diagram. -/
def terminalChartTailIso (D : I ⥤ Over X) (i : I) :
    chartTail D i (Over.mk (𝟙 (D.obj i).left)) ≅ Over.forget i ⋙ D :=
  NatIso.ofComponents (fun j ↦ by
    have : IsIso (Over.mk (𝟙 (D.obj i).left)).hom :=
      inferInstanceAs (IsIso (𝟙 (D.obj i).left))
    have h : IsIso (Limits.pullback.fst (D.map j.hom).left (Over.mk (𝟙 (D.obj i).left)).hom) :=
      (IsPullback.of_hasPullback (D.map j.hom).left
        (Over.mk (𝟙 (D.obj i).left)).hom).isIso_fst_of_isIso
    let e : Limits.pullback (D.map j.hom).left (Over.mk (𝟙 (D.obj i).left)).hom ≅
        (D.obj j.left).left :=
      @asIso C _ _ _
        (Limits.pullback.fst (D.map j.hom).left (Over.mk (𝟙 (D.obj i).left)).hom) h
    exact Over.isoMk e (by
      change Limits.pullback.fst (D.map j.hom).left (Over.mk (𝟙 (D.obj i).left)).hom ≫
        (D.obj j.left).hom =
        Limits.pullback.snd (D.map j.hom).left (Over.mk (𝟙 (D.obj i).left)).hom ≫
          (Over.mk (𝟙 (D.obj i).left)).hom ≫ (D.obj i).hom
      exact (congrArg
        (fun z ↦ Limits.pullback.fst (D.map j.hom).left (Over.mk (𝟙 (D.obj i).left)).hom ≫ z)
        (Over.w (D.map j.hom)).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z ↦ z ≫ (D.obj i).hom) Limits.pullback.condition).trans
            (Category.assoc _ _ _))))) (by
    intro j k a
    apply Over.OverMorphism.ext
    exact chartTail_map_fst D i (Over.mk (𝟙 (D.obj i).left)) a)

/-- The native terminal limit chart is identified by its actual second projection. -/
def terminalLimitChartIso (D : I ⥤ Over X) (c : Cone D) (i : I) :
    (nativeLimitChartFunctor D c i).obj (Over.mk (𝟙 (D.obj i).left)) ≅ c.pt := by
  have : IsIso (Over.mk (𝟙 (D.obj i).left)).hom :=
    inferInstanceAs (IsIso (𝟙 (D.obj i).left))
  have h : IsIso (Limits.pullback.snd (Over.mk (𝟙 (D.obj i).left)).hom (c.π.app i).left) :=
    (IsPullback.of_hasPullback (Over.mk (𝟙 (D.obj i).left)).hom
      (c.π.app i).left).isIso_snd_of_isIso
  let e : Limits.pullback (Over.mk (𝟙 (D.obj i).left)).hom (c.π.app i).left ≅ c.pt.left :=
    @asIso C _ _ _
      (Limits.pullback.snd (Over.mk (𝟙 (D.obj i).left)).hom (c.π.app i).left) h
  exact Over.isoMk e

/-- Terminal normalization respects the original limit-cone legs. -/
theorem terminalChartTailCone_triangle (D : I ⥤ Over X) (c : Cone D) (i : I)
    (j : Over i) :
    (nativeChartTailCone D c i (Over.mk (𝟙 (D.obj i).left))).π.app j ≫
      (terminalChartTailIso D i).hom.app j =
      (terminalLimitChartIso D c i).hom ≫ c.π.app j.left := by
  apply Over.OverMorphism.ext
  exact nativeChartTailCone_π_fst D c i (Over.mk (𝟙 (D.obj i).left)) j

end CategoryTheory.Over.ChartTails
