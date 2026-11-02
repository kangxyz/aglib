/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.Core
public import Aglib.AlgebraicGeometry.Curves.Abel.GraphPointClasses
public import Aglib.AlgebraicGeometry.Curves.Abel.Degree
public import Aglib.AlgebraicGeometry.Curves.Abel.Naturality
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula
public import Aglib.AlgebraicGeometry.Limits.FiniteProducts
public import Aglib.AlgebraicGeometry.Modules.Invertible.FiniteTensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.RelativeFlat
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Properties
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Properties.Normal.Components

/-! # The actual ordered graph-sum line-bundle family

The parameter scheme is the existing finite native product in `Over S`.
On the actual product curve, tensor the original graph-difference bundles
of its coordinates. The empty parameter is the actual base and the empty
bundle is the existing trivial line bundle.

Original coordinate lifts, original Picard pullbacks and original graph
base-change maps give specialization to each actual ordered tuple. Fibre
degree zero holds over arbitrary fields, using the proved finite Cartier
degree theorem, not algebraically closed residue-field weights.

This constructs the actual coefficient bundle needed for semicontinuity.
It does not construct a torsion locus, trivialize its power, assert Picard
representability, prove finiteness, or use proper base change.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {S X : Scheme.{u}} (p : X ⟶ S)

variable [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- On the actual field fibre, specialization is the original point-divisor
class difference for each coordinate, in arbitrary genus. -/
theorem lineBundle_class_at_field_tuple
    {k : Type u} [Field k] (t : Spec (.of k) ⟶ S) {n : ℕ}
    (s : Fin n → (Spec (.of k) ⟶ X)) (hs : ∀ i, s i ≫ p = t)
    (hY : Properties (Over.mk (pullback.snd p t)))
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) p t) ≤ 1) :
    let Y : FScheme k := Over.mk (pullback.snd p t)
    letI := PointDivisor.isIntegral_of_properties Y hY
    letI := curveProperties_isNoetherian hY
    letI (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
    pullbackClass (Hom.familyMap p (parameter p n).hom t (parameterPoint p t s hs)
      (parameterPoint_over p t s hs)) (classOf _ (lineBundle p o ho n)) =
        ∑ i, Picard.DivisorClass.divisorToPicard Y.left hdim
          (PointDivisor.pointDivisor Y (Hom.graph p t (s i) (hs i))
            (Hom.graph_snd p t (s i) (hs i)) 1 -
          PointDivisor.pointDivisor Y (Hom.graph p t (t ≫ o) (by simp [Category.assoc, ho]))
            (Hom.graph_snd p t _ _) 1) := by
  let Y : FScheme k := Over.mk (pullback.snd p t)
  let := PointDivisor.isIntegral_of_properties Y hY
  let := curveProperties_isNoetherian hY
  let (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
  rw [lineBundle_class_at_tuple]
  apply Finset.sum_congr rfl
  intro i hi
  exact Abel.abelClass_eq_pointDifference p o ho t (s i) (hs i) hY hdim

/-- Every actual field specialization has original degree zero. The field
need not be algebraically closed; each graph is a rational degree-one point. -/
theorem lineBundle_degree_at_field_tuple
    {k : Type u} [Field k] (t : Spec (.of k) ⟶ S) {n : ℕ}
    (s : Fin n → (Spec (.of k) ⟶ X)) (hs : ∀ i, s i ≫ p = t)
    (hY : Properties (Over.mk (pullback.snd p t))) :
    curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      (Over.mk (pullback.snd p t)) hY
      (pullbackClass (Hom.familyMap p (parameter p n).hom t (parameterPoint p t s hs)
        (parameterPoint_over p t s hs)) (classOf _ (lineBundle p o ho n))) = 0 := by
  rw [lineBundle_class_at_tuple, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact Abel.curveDegree_abelClass smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Picard.Degree.properCurveProductFormula FiniteCartierDegree.finiteCartierIdealDegree
    Hom.smoothRelativeDivisorIdeal p o ho t (s i) (hs i) hY

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
