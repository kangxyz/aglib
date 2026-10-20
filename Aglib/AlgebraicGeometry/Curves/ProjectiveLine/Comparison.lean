/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.TwoChart

/-!
# Coordinate-preserving comparison of two projective-line models

The canonical isomorphism compares the literal polynomial pushout with homogeneous
Proj, preserving both chart arrows and the original structural map. The migrated
source is the pure geometry suffix of
`R5Lab.Aglib.AlgebraicGeometry.Curves.Cohomology.ProperCurves.ProjectiveLine`,
lines 218–347 at R5Lab revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
No Laurent-module or cohomological-finiteness input is used.
-/

@[expose] public section

universe u

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart

open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PolynomialLaurent

variable (K : Type u) [Field K]

lemma twoChartLine_chart_compatibility :
    laurentPlus (.of K) ≫ ProjectiveLine.chart K 0 =
      laurentMinus (.of K) ≫ ProjectiveLine.chart K 1 := by
  have h := ProjectiveLine.chart_transition K (LaurentPolynomial K)
    (laurentCoordinateUnit (.of K))
  have hp : (Polynomial.aeval (↑(laurentCoordinateUnit (.of K)) : LaurentPolynomial K)).toRingHom =
      Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp [laurentCoordinateUnit]
  have hm : (Polynomial.aeval (↑(laurentCoordinateUnit (.of K))⁻¹ : LaurentPolynomial
    K)).toRingHom =
      LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp [laurentCoordinateUnit]
  simpa only [hp, hm, laurentPlus, laurentMinus] using h

lemma twoChartLine_chart_preimage :
    ProjectiveLine.chart K 0 ⁻¹ᵁ (ProjectiveLine.chart K 1).opensRange =
      (laurentPlus (.of K)).opensRange := by
  rw [ProjectiveLine.chart_opensRange,
    ProjectiveLine.chart_preimage_linear K 0 _ (MvPolynomial.isHomogeneous_X K 1),
    laurentPlus_opensRange]
  simp [ProjectiveLine.dehomogenizePolynomial]

/-- The map from the original two-chart gluing to the actual homogeneous Proj. -/
def twoChartLineToProjectiveP1 :
    _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.twoChartLine (.of K) ⟶
      ProjectiveLine.projectiveP1 K :=
  pushout.desc (ProjectiveLine.chart K 0) (ProjectiveLine.chart K 1)
    (twoChartLine_chart_compatibility K)

instance twoChartLineToProjectiveP1_isIso : IsIso (twoChartLineToProjectiveP1 K) := by
  apply OpenPushoutIso.desc_isIso (laurentPlus (.of K)) (laurentMinus (.of K))
    (ProjectiveLine.chart K 0) (ProjectiveLine.chart K 1)
    (twoChartLine_chart_compatibility K) (twoChartLine_chart_preimage K)
  intro z
  obtain ⟨i, x, hx⟩ := ProjectiveLine.chart_covered K z
  fin_cases i
  · exact Or.inl ⟨x, hx⟩
  · exact Or.inr ⟨x, hx⟩

/-- The canonical actual scheme isomorphism, preserving both original coordinates. -/
def twoChartLineIsoProjectiveP1 :
    _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.twoChartLine (.of K) ≅
      ProjectiveLine.projectiveP1 K :=
  asIso (twoChartLineToProjectiveP1 K)

@[reassoc (attr := simp)] theorem twoChartLineIsoProjectiveP1_plusChart :
    _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.plusChart (.of K) ≫
      (twoChartLineIsoProjectiveP1 K).hom =
      ProjectiveLine.chart K 0 :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem twoChartLineIsoProjectiveP1_minusChart :
    _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.minusChart (.of K) ≫
      (twoChartLineIsoProjectiveP1 K).hom =
      ProjectiveLine.chart K 1 :=
  pushout.inr_desc _ _ _

@[reassoc] theorem twoChartLineIsoProjectiveP1_over :
    (twoChartLineIsoProjectiveP1 K).hom ≫ ProjectiveLine.structureMap K =
      _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.projection (.of K) := by
  apply pushout.hom_ext
  · change _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.plusChart (.of K) ≫
      ((twoChartLineIsoProjectiveP1 K).hom ≫ ProjectiveLine.structureMap K) =
      _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.plusChart (.of K) ≫
        _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.projection (.of K)
    rw [← Category.assoc, twoChartLineIsoProjectiveP1_plusChart, ProjectiveLine.chart_over,
      _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.plusChart_projection]
    rfl
  · change _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.minusChart (.of K) ≫
      ((twoChartLineIsoProjectiveP1 K).hom ≫ ProjectiveLine.structureMap K) =
      _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.minusChart (.of K) ≫
        _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.projection (.of K)
    rw [← Category.assoc, twoChartLineIsoProjectiveP1_minusChart, ProjectiveLine.chart_over,
      _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.minusChart_projection]
    rfl

@[reassoc (attr := simp)] theorem twoChartLineIsoProjectiveP1_chart_zero_inv :
    ProjectiveLine.chart K 0 ≫ (twoChartLineIsoProjectiveP1 K).inv =
      _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.plusChart (.of K) := by
  rw [← twoChartLineIsoProjectiveP1_plusChart, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

@[reassoc (attr := simp)] theorem twoChartLineIsoProjectiveP1_chart_one_inv :
    ProjectiveLine.chart K 1 ≫ (twoChartLineIsoProjectiveP1 K).inv =
      _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.minusChart (.of K) := by
  rw [← twoChartLineIsoProjectiveP1_minusChart, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

@[reassoc] theorem twoChartLineIsoProjectiveP1_inv_over :
    (twoChartLineIsoProjectiveP1 K).inv ≫
      _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.projection (.of K) =
        ProjectiveLine.structureMap K := by
  rw [← twoChartLineIsoProjectiveP1_over, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The comparison as an isomorphism in the category of actual `K`-schemes. -/
def twoChartLineOverIsoProjectiveP1 :
    Over.mk (_root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.projection (.of K)) ≅
      Over.mk (ProjectiveLine.structureMap K) :=
  Over.isoMk (twoChartLineIsoProjectiveP1 K) (twoChartLineIsoProjectiveP1_over K)

end AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart

noncomputable section
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart
variable (K : Type u) [Field K]
/-- Properness of the original two-chart projection, transported through the actual
base-preserving isomorphism. -/
instance twoChartLine_projection_isProper :
    IsProper (_root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart.projection (.of K)) := by
  rw [← twoChartLineIsoProjectiveP1_over K]
  infer_instance
end AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart
