/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing
public import Aglib.CategoryTheory.Over.ChartTails
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
/-! # Actual affine chart tails over the original coefficient base -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u
variable {I : Type u} [Category.{u} I] {X : Scheme.{u}}

/-- Actual pullbacks of a stage chart, still over the original base scheme. -/
def relativeChartTail (D : I ⥤ Over X) (i : I) (U : (D.obj i).left.Etale) :
    Over i ⥤ Over X :=
  Over.ChartTails.chartTail D i ((Etale.forget _).obj U)

/-- The original limit cone base-changed to a stage chart and retained over the base. -/
def relativeChartTailCone (D : I ⥤ Over X) (c : Cone D) (i : I)
    (U : (D.obj i).left.Etale) : Cone (relativeChartTail D i U) :=
  Over.ChartTails.chartTailCone D c i ((Etale.forget _).obj U)

/-- The supplied underlying scheme limit remains the actual chart-tail limit. -/
def relativeChartTailConeIsLimit [IsCofiltered I]
    (D : I ⥤ Over X) (c : Cone D) (hc : IsLimit ((Over.forget X).mapCone c))
    (i : I) (U : (D.obj i).left.Etale) :
    IsLimit ((Over.forget X).mapCone (relativeChartTailCone D c i U)) :=
  Over.ChartTails.chartTailConeIsLimit D c hc i ((Etale.forget _).obj U)

/-- Affine transitions make the actual pullback stages of an affine chart affine. -/
instance relativeChartTail_isAffine_obj (D : I ⥤ Over X)
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (i : I) (U : (D.obj i).left.Etale) [IsAffine U.left] (j : Over i) :
    IsAffine ((relativeChartTail D i U).obj j).left := by
  change IsAffine (pullback (D.map j.hom).left U.hom)
  have : IsAffineHom (pullback.snd (D.map j.hom).left U.hom) :=
    @MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@IsAffineHom) isAffineHom_isStableUnderBaseChange
      U.left (D.obj j.left).left (pullback (D.map j.hom).left U.hom) (D.obj i).left
      U.hom (D.map j.hom).left
      (pullback.fst (D.map j.hom).left U.hom) (pullback.snd (D.map j.hom).left U.hom)
      (IsPullback.of_hasPullback (D.map j.hom).left U.hom)
      (inferInstance : IsAffineHom (D.map j.hom).left)
  have : IsAffine ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsAffine U.left)
  exact isAffine_of_isAffineHom (pullback.snd (D.map j.hom).left U.hom)

/-- The native chart-tail projection has the original first pullback projection. -/
theorem relativeChartTailCone_π_fst (D : I ⥤ Over X) (c : Cone D)
    (i : I) (U : (D.obj i).left.Etale) (j : Over i) :
    ((relativeChartTailCone D c i U).π.app j).left ≫
        pullback.fst (D.map j.hom).left U.hom =
      pullback.fst (c.π.app i).left U.hom ≫ (c.π.app j.left).left := by
  exact Over.ChartTails.chartTailCone_π_fst D c i ((Etale.forget _).obj U) j

/-- The native chart-tail projection preserves the original chart coordinate. -/
theorem relativeChartTailCone_π_snd (D : I ⥤ Over X) (c : Cone D)
    (i : I) (U : (D.obj i).left.Etale) (j : Over i) :
    ((relativeChartTailCone D c i U).π.app j).left ≫
        pullback.snd (D.map j.hom).left U.hom =
      pullback.snd (c.π.app i).left U.hom := by
  exact Over.ChartTails.chartTailCone_π_snd D c i ((Etale.forget _).obj U) j

/-- The original tail arrow preserves the stage coordinate. -/
@[reassoc]
theorem relativeChartTail_map_fst (D : I ⥤ Over X) (i : I)
    (U : (D.obj i).left.Etale) {j k : Over i} (a : j ⟶ k) :
    ((relativeChartTail D i U).map a).left ≫ pullback.fst (D.map k.hom).left U.hom =
      pullback.fst (D.map j.hom).left U.hom ≫ (D.map a.left).left := by
  exact Over.ChartTails.chartTail_map_fst D i ((Etale.forget _).obj U) a

/-- The original tail arrow preserves the chart coordinate. -/
@[reassoc]
theorem relativeChartTail_map_snd (D : I ⥤ Over X) (i : I)
    (U : (D.obj i).left.Etale) {j k : Over i} (a : j ⟶ k) :
    ((relativeChartTail D i U).map a).left ≫ pullback.snd (D.map k.hom).left U.hom =
      pullback.snd (D.map j.hom).left U.hom := by
  exact Over.ChartTails.chartTail_map_snd D i ((Etale.forget _).obj U) a

/-- An original chart morphism gives its actual stage pullback map over the base. -/
def relativeChartTailMapApp (D : I ⥤ Over X) (i : I)
    {U V : (D.obj i).left.Etale} (a : U ⟶ V) (j : Over i) :
    (relativeChartTail D i U).obj j ⟶ (relativeChartTail D i V).obj j :=
  Over.ChartTails.chartTailMapApp D i ((Etale.forget _).map a) j

@[reassoc]
theorem relativeChartTailMapApp_fst (D : I ⥤ Over X) (i : I)
    {U V : (D.obj i).left.Etale} (a : U ⟶ V) (j : Over i) :
    (relativeChartTailMapApp D i a j).left ≫ pullback.fst (D.map j.hom).left V.hom =
      pullback.fst (D.map j.hom).left U.hom := by
  exact Over.ChartTails.chartTailMapApp_fst D i ((Etale.forget _).map a) j

@[reassoc]
theorem relativeChartTailMapApp_snd (D : I ⥤ Over X) (i : I)
    {U V : (D.obj i).left.Etale} (a : U ⟶ V) (j : Over i) :
    (relativeChartTailMapApp D i a j).left ≫ pullback.snd (D.map j.hom).left V.hom =
      pullback.snd (D.map j.hom).left U.hom ≫ a.left := by
  exact Over.ChartTails.chartTailMapApp_snd D i ((Etale.forget _).map a) j

/-- Chart morphisms act naturally on actual relative chart tails. -/
def relativeChartTailMap (D : I ⥤ Over X) (i : I)
    {U V : (D.obj i).left.Etale} (a : U ⟶ V) :
    relativeChartTail D i U ⟶ relativeChartTail D i V :=
  Over.ChartTails.chartTailMap D i ((Etale.forget _).map a)

/-- The original stage étale site acts functorially on its actual relative tails. -/
def relativeChartTails (D : I ⥤ Over X) (i : I) :
    (D.obj i).left.Etale ⥤ (Over i ⥤ Over X) :=
  Etale.forget (D.obj i).left ⋙ Over.ChartTails.chartTails D i

end AlgebraicGeometry.Scheme.EtaleAffineBasis
