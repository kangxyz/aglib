/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.ClosedStalks
public import Aglib.AlgebraicGeometry.Curves.AlgebraicallyClosedGeometry
public import Aglib.AlgebraicGeometry.Curves.Genus.BaseChange
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Comparison
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Integral
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula
public import Aglib.AlgebraicGeometry.Curves.Picard.NormDegree.OrderFormula
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.LineBundle
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.HighDegreeVanishing
public import Aglib.AlgebraicGeometry.Curves.RiemannHurwitz.CanonicalDegree
public import Aglib.AlgebraicGeometry.Curves.GenusOneGroupLaw

/-!
# Native curve providers on their original objects

These public-interface examples retain arbitrary fields and same-universe
schemes, original structural maps, prescribed origins and the full theorem-family
conditions. The genus-one group-law entry still has its representability premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {F : Type u} [Field F] {X : FScheme F}

example (hX : Properties X) (K : Type u) [Field K]
    (s : Spec (.of K) ⟶ Base F) :
    Properties (Over.mk (pullback.snd X.hom s)) :=
  curveProperties_baseChange hX K s

example (o : 𝟙_ (FScheme F) ⟶ X) (law : PointedGroupLaw X o) :
    @MonObj.one _ _ _ X law.law.toMonObj = o := law.origin

example (K : Type u) [Field K] :
    Scheme.ProjectiveLine.TwoChart.plusChart (.of K) ≫
        (Scheme.ProjectiveLine.TwoChart.twoChartLineIsoProjectiveP1 K).hom =
      Scheme.ProjectiveLine.chart K 0 :=
  Scheme.ProjectiveLine.TwoChart.twoChartLineIsoProjectiveP1_plusChart K

example : Picard.Degree.ProperCurveProductFormula.{u} :=
  Picard.Degree.properCurveProductFormula

example : LineBundleRiemannRoch.{u} := lineBundleRiemannRoch

example : Picard.NormDegree.FiniteMorphismNormOrder.{u} :=
  Picard.NormDegree.finiteMorphismNormOrder

example : SmoothCanonicalDegree.{u} := smoothCanonicalDegree

example : LineBundleHighDegreeVanishing.{u} := lineBundleHighDegreeVanishing

#check Projectivity.exists_projectiveEmbedding
#check RelativePicard.DegreeZeroPicardRepresentability
#check genusOnePointedGroupLaw
