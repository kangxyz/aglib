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
  Over.ChartTails.nativeLimitChartIso D c i ((Etale.forget _).obj U)

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
  exact Over.ChartTails.nativeChartTailCone_π_fst D c i ((Etale.forget _).obj U) j

@[reassoc]
theorem nativeChartTailCone_π_snd (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : (D.obj i).left.Etale) (j : Over i) :
    ((nativeChartTailCone D c i U).π.app j).left ≫
      pullback.snd (D.map j.hom).left U.hom = pullback.fst U.hom (c.π.app i).left := by
  exact Over.ChartTails.nativeChartTailCone_π_snd D c i ((Etale.forget _).obj U) j

/-- The original oriented cone retains the actual underlying scheme limit. -/
def nativeChartTailConeIsLimit [IsCofiltered I] (D : I ⥤ Over X) (c : Cone D)
    (hc : IsLimit ((Over.forget X).mapCone c)) (i : I) (U : (D.obj i).left.Etale) :
    IsLimit ((Over.forget X).mapCone (nativeChartTailCone D c i U)) :=
  Over.ChartTails.nativeChartTailConeIsLimit D c hc i ((Etale.forget _).obj U)

/-- The cone leg is natural in the original chart variable. -/
def nativeChartTailLeg (D : I ⥤ Over X) (c : Cone D) (i : I) (j : Over i) :
    nativeLimitChartFunctor D c i ⟶ (relativeChartTails D i).flip.obj j :=
  Functor.whiskerLeft (Etale.forget _) (Over.ChartTails.nativeChartTailLeg D c i j)

/-- One cone in the chart-functor category, not unrelated objectwise choices. -/
def nativeChartTailsCone (D : I ⥤ Over X) (c : Cone D) (i : I) :
    Cone (relativeChartTails D i).flip :=
  ((Functor.whiskeringLeft _ _ _).obj (Etale.forget (D.obj i).left)).mapCone
    (Over.ChartTails.nativeChartTailsCone D c i)

/-- Original stage-site base change, retained over the coefficient base. -/
def nativeStageChartFunctor (D : I ⥤ Over X) (i : I) (j : Over i) :
    (D.obj i).left.Etale ⥤ Over X :=
  siteBaseChange (D.map j.hom).left ⋙ Etale.forget (D.obj j.left).left ⋙
    Over.map (D.obj j.left).hom

/-- The stage comparison keeps the actual pullback-symmetry map. -/
def nativeStageChartIso (D : I ⥤ Over X) (i : I) (j : Over i)
    (U : (D.obj i).left.Etale) :
    (nativeStageChartFunctor D i j).obj U ≅ (relativeChartTail D i U).obj j :=
  Over.ChartTails.nativeStageChartIso D i j ((Etale.forget _).obj U)

/-- The actual stage-orientation comparison is natural in the original chart. -/
def nativeStageChartsIso (D : I ⥤ Over X) (i : I) (j : Over i) :
    nativeStageChartFunctor D i j ≅ (relativeChartTails D i).flip.obj j :=
  Functor.isoWhiskerLeft (Etale.forget _) (Over.ChartTails.nativeStageChartsIso D i j)

/-- At the terminal chart the actual tail recovers the original stage-tail diagram. -/
def terminalChartTailIso (D : I ⥤ Over X) (i : I) :
    relativeChartTail D i (etaleTerminal (D.obj i).left) ≅ Over.forget i ⋙ D :=
  Over.ChartTails.terminalChartTailIso D i

/-- The native terminal limit chart is identified by its actual second projection. -/
def terminalLimitChartIso (D : I ⥤ Over X) (c : Cone D) (i : I) :
    (nativeLimitChartFunctor D c i).obj (etaleTerminal (D.obj i).left) ≅ c.pt :=
  Over.ChartTails.terminalLimitChartIso D c i

/-- Terminal normalization respects the original limit-cone legs. -/
theorem terminalChartTailCone_triangle (D : I ⥤ Over X) (c : Cone D) (i : I)
    (j : Over i) :
    (nativeChartTailCone D c i (etaleTerminal (D.obj i).left)).π.app j ≫
      (terminalChartTailIso D i).hom.app j =
      (terminalLimitChartIso D c i).hom ≫ c.π.app j.left := by
  exact Over.ChartTails.terminalChartTailCone_triangle D c i j

end AlgebraicGeometry.Scheme.EtaleAffineBasis
