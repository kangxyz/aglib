/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RelativeChartTails
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
/-! # The original limit-chart cone, natural in the étale chart -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u
open EtaleCohomology
variable {I : Type u} [Category.{u} I] {X : Scheme.{u}}

/-- Original base change of charts to the supplied limit, retained over X. -/
def nativeLimitChartFunctor (D : I ⥤ Over X) (c : Cone D) (i : I) :
    (D.obj i).left.Etale ⥤ Over X :=
  siteBaseChange (c.π.app i).left ⋙ Etale.forget c.pt.left ⋙ Over.map c.pt.hom

/-- The original site's pullback orientation is identified with the actual tail limit. -/
def nativeLimitChartIso (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : (D.obj i).left.Etale) :
    (nativeLimitChartFunctor D c i).obj U ≅ (relativeChartTailCone D c i U).pt :=
  Over.isoMk (pullbackSymmetry U.hom (c.π.app i).left) (by
    change (pullbackSymmetry U.hom (c.π.app i).left).hom ≫
      (pullback.snd (c.π.app i).left U.hom ≫ U.hom ≫ (D.obj i).hom) =
      pullback.snd U.hom (c.π.app i).left ≫ c.pt.hom
    exact (pullbackSymmetry_hom_comp_snd_assoc _ _ _).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ (D.obj i).hom) pullback.condition).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ pullback.snd U.hom (c.π.app i).left ≫ z) (Over.w (c.π.app i)))))))

/-- Actual chart-tail cone with the original site-base-change object as its point. -/
def nativeChartTailCone (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : (D.obj i).left.Etale) : Cone (relativeChartTail D i U) :=
  (relativeChartTailCone D c i U).extend (nativeLimitChartIso D c i U).hom

@[reassoc]
theorem nativeChartTailCone_π_fst (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : (D.obj i).left.Etale) (j : Over i) :
    ((nativeChartTailCone D c i U).π.app j).left ≫
      pullback.fst (D.map j.hom).left U.hom =
      pullback.snd U.hom (c.π.app i).left ≫ (c.π.app j.left).left := by
  change ((pullbackSymmetry U.hom (c.π.app i).left).hom ≫
    ((relativeChartTailCone D c i U).π.app j).left) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ (pullbackSymmetry U.hom (c.π.app i).left).hom ≫ z)
      (relativeChartTailCone_π_fst D c i U j)).trans
      (pullbackSymmetry_hom_comp_fst_assoc _ _ _))

@[reassoc]
theorem nativeChartTailCone_π_snd (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : (D.obj i).left.Etale) (j : Over i) :
    ((nativeChartTailCone D c i U).π.app j).left ≫
      pullback.snd (D.map j.hom).left U.hom = pullback.fst U.hom (c.π.app i).left := by
  change ((pullbackSymmetry U.hom (c.π.app i).left).hom ≫
    ((relativeChartTailCone D c i U).π.app j).left) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ (pullbackSymmetry U.hom (c.π.app i).left).hom ≫ z)
      (relativeChartTailCone_π_snd D c i U j)).trans
      (pullbackSymmetry_hom_comp_snd _ _))

/-- The original oriented cone retains the actual underlying scheme limit. -/
def nativeChartTailConeIsLimit [IsCofiltered I] (D : I ⥤ Over X) (c : Cone D)
    (hc : IsLimit ((Over.forget X).mapCone c)) (i : I) (U : (D.obj i).left.Etale) :
    IsLimit ((Over.forget X).mapCone (nativeChartTailCone D c i U)) := by
  let e := (Over.forget X).mapIso (nativeLimitChartIso D c i U)
  exact (relativeChartTailConeIsLimit D c hc i U).ofIsoLimit
    (Cone.extendIso ((Over.forget X).mapCone (relativeChartTailCone D c i U)) e.symm)

/-- The cone leg is natural in the original chart variable. -/
def nativeChartTailLeg (D : I ⥤ Over X) (c : Cone D) (i : I) (j : Over i) :
    nativeLimitChartFunctor D c i ⟶ (relativeChartTails D i).flip.obj j where
  app U := (nativeChartTailCone D c i U).π.app j
  naturality {U V} a := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (((siteBaseChange (c.π.app i).left).map a).left ≫
        ((nativeChartTailCone D c i V).π.app j).left) ≫ _ =
        (((nativeChartTailCone D c i U).π.app j).left ≫
          (relativeChartTailMapApp D i a j).left) ≫ _
      exact ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ ((siteBaseChange (c.π.app i).left).map a).left ≫ z)
          (nativeChartTailCone_π_fst D c i V j)).trans
          (siteBaseChange_map_snd_assoc (c.π.app i).left a _))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ ((nativeChartTailCone D c i U).π.app j).left ≫ z)
            (relativeChartTailMapApp_fst D i a j)).trans
            (nativeChartTailCone_π_fst D c i U j))).symm
    · change (((siteBaseChange (c.π.app i).left).map a).left ≫
        ((nativeChartTailCone D c i V).π.app j).left) ≫ _ =
        (((nativeChartTailCone D c i U).π.app j).left ≫
          (relativeChartTailMapApp D i a j).left) ≫ _
      exact ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ ((siteBaseChange (c.π.app i).left).map a).left ≫ z)
          (nativeChartTailCone_π_snd D c i V j)).trans
          (siteBaseChange_map_fst (c.π.app i).left a))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ ((nativeChartTailCone D c i U).π.app j).left ≫ z)
            (relativeChartTailMapApp_snd D i a j)).trans
            (nativeChartTailCone_π_snd_assoc D c i U j a.left))).symm

/-- One cone in the chart-functor category, not unrelated objectwise choices. -/
def nativeChartTailsCone (D : I ⥤ Over X) (c : Cone D) (i : I) :
    Cone (relativeChartTails D i).flip where
  pt := nativeLimitChartFunctor D c i
  π :=
    { app := nativeChartTailLeg D c i
      naturality {j k} a := by
        apply NatTrans.ext
        funext U
        change (𝟙 _) ≫ (nativeChartTailCone D c i U).π.app k =
          (nativeChartTailCone D c i U).π.app j ≫ (relativeChartTail D i U).map a
        exact (Category.id_comp _).trans ((nativeChartTailCone D c i U).w a).symm }

/-- Original stage-site base change, retained over the coefficient base. -/
def nativeStageChartFunctor (D : I ⥤ Over X) (i : I) (j : Over i) :
    (D.obj i).left.Etale ⥤ Over X :=
  siteBaseChange (D.map j.hom).left ⋙ Etale.forget (D.obj j.left).left ⋙
    Over.map (D.obj j.left).hom

/-- The stage comparison keeps the actual pullback-symmetry map. -/
def nativeStageChartIso (D : I ⥤ Over X) (i : I) (j : Over i)
    (U : (D.obj i).left.Etale) :
    (nativeStageChartFunctor D i j).obj U ≅ (relativeChartTail D i U).obj j :=
  Over.isoMk (pullbackSymmetry U.hom (D.map j.hom).left) (by
    change (pullbackSymmetry U.hom (D.map j.hom).left).hom ≫
      (pullback.snd (D.map j.hom).left U.hom ≫ U.hom ≫ (D.obj i).hom) =
      pullback.snd U.hom (D.map j.hom).left ≫ (D.obj j.left).hom
    exact (pullbackSymmetry_hom_comp_snd_assoc _ _ _).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ (D.obj i).hom) pullback.condition).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ pullback.snd U.hom (D.map j.hom).left ≫ z)
            (Over.w (D.map j.hom)))))))

/-- The actual stage-orientation comparison is natural in the original chart. -/
def nativeStageChartsIso (D : I ⥤ Over X) (i : I) (j : Over i) :
    nativeStageChartFunctor D i j ≅ (relativeChartTails D i).flip.obj j :=
  NatIso.ofComponents (nativeStageChartIso D i j) (by
    intro U V a
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (((siteBaseChange (D.map j.hom).left).map a).left ≫
        (pullbackSymmetry V.hom (D.map j.hom).left).hom) ≫ _ =
        ((pullbackSymmetry U.hom (D.map j.hom).left).hom ≫
          (relativeChartTailMapApp D i a j).left) ≫ _
      exact ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ ((siteBaseChange (D.map j.hom).left).map a).left ≫ z)
          (pullbackSymmetry_hom_comp_fst V.hom (D.map j.hom).left)).trans
          (siteBaseChange_map_snd (D.map j.hom).left a))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ (pullbackSymmetry U.hom (D.map j.hom).left).hom ≫ z)
            (relativeChartTailMapApp_fst D i a j)).trans
            (pullbackSymmetry_hom_comp_fst _ _))).symm
    · change (((siteBaseChange (D.map j.hom).left).map a).left ≫
        (pullbackSymmetry V.hom (D.map j.hom).left).hom) ≫ _ =
        ((pullbackSymmetry U.hom (D.map j.hom).left).hom ≫
          (relativeChartTailMapApp D i a j).left) ≫ _
      exact ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ ((siteBaseChange (D.map j.hom).left).map a).left ≫ z)
          (pullbackSymmetry_hom_comp_snd V.hom (D.map j.hom).left)).trans
          (siteBaseChange_map_fst (D.map j.hom).left a))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ (pullbackSymmetry U.hom (D.map j.hom).left).hom ≫ z)
            (relativeChartTailMapApp_snd D i a j)).trans
            (pullbackSymmetry_hom_comp_snd_assoc _ _ a.left))).symm)

/-- At the terminal chart the actual tail recovers the original stage-tail diagram. -/
def terminalChartTailIso (D : I ⥤ Over X) (i : I) :
    relativeChartTail D i (etaleTerminal (D.obj i).left) ≅ Over.forget i ⋙ D :=
  NatIso.ofComponents (fun j ↦ by
    have : IsIso (etaleTerminal (D.obj i).left).hom :=
      inferInstanceAs (IsIso (𝟙 (D.obj i).left))
    have h : IsIso (pullback.fst (D.map j.hom).left (etaleTerminal (D.obj i).left).hom) :=
      (IsPullback.of_hasPullback (D.map j.hom).left
        (etaleTerminal (D.obj i).left).hom).isIso_fst_of_isIso
    let e : pullback (D.map j.hom).left (etaleTerminal (D.obj i).left).hom ≅
        (D.obj j.left).left :=
      @asIso Scheme.{u} _ _ _
        (pullback.fst (D.map j.hom).left (etaleTerminal (D.obj i).left).hom) h
    exact Over.isoMk e (by
      change pullback.fst (D.map j.hom).left (etaleTerminal (D.obj i).left).hom ≫
        (D.obj j.left).hom =
        pullback.snd (D.map j.hom).left (etaleTerminal (D.obj i).left).hom ≫
          (etaleTerminal (D.obj i).left).hom ≫ (D.obj i).hom
      exact (congrArg
        (fun z ↦ pullback.fst (D.map j.hom).left (etaleTerminal (D.obj i).left).hom ≫ z)
        (Over.w (D.map j.hom)).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z ↦ z ≫ (D.obj i).hom) pullback.condition).trans
            (Category.assoc _ _ _))))) (by
    intro j k a
    apply Over.OverMorphism.ext
    exact relativeChartTail_map_fst D i (etaleTerminal (D.obj i).left) a)

/-- The native terminal limit chart is identified by its actual second projection. -/
def terminalLimitChartIso (D : I ⥤ Over X) (c : Cone D) (i : I) :
    (nativeLimitChartFunctor D c i).obj (etaleTerminal (D.obj i).left) ≅ c.pt := by
  have : IsIso (etaleTerminal (D.obj i).left).hom :=
    inferInstanceAs (IsIso (𝟙 (D.obj i).left))
  have h : IsIso (pullback.snd (etaleTerminal (D.obj i).left).hom (c.π.app i).left) :=
    (IsPullback.of_hasPullback (etaleTerminal (D.obj i).left).hom
      (c.π.app i).left).isIso_snd_of_isIso
  let e : pullback (etaleTerminal (D.obj i).left).hom (c.π.app i).left ≅ c.pt.left :=
    @asIso Scheme.{u} _ _ _
      (pullback.snd (etaleTerminal (D.obj i).left).hom (c.π.app i).left) h
  exact Over.isoMk e

/-- Terminal normalization respects the original limit-cone legs. -/
theorem terminalChartTailCone_triangle (D : I ⥤ Over X) (c : Cone D) (i : I)
    (j : Over i) :
    (nativeChartTailCone D c i (etaleTerminal (D.obj i).left)).π.app j ≫
      (terminalChartTailIso D i).hom.app j =
      (terminalLimitChartIso D c i).hom ≫ c.π.app j.left := by
  apply Over.OverMorphism.ext
  exact nativeChartTailCone_π_fst D c i (etaleTerminal (D.obj i).left) j

end AlgebraicGeometry.Scheme.EtaleAffineBasis
