/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.PointDivisor.Basic
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphLineBundle
public import Aglib.AlgebraicGeometry.IdealSheaf.Modules

/-! # Original point ideals and divisor classes in arbitrary genus

The published point-ideal divisor calculation identifies the actual positive
point class, not only its degree. No genus-one normalization, Picard
representability, or cohomological finiteness input is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve.Picard
open AlgebraicGeometry.Scheme.OverField.Curve.Abel.FiniteCartierDegree

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

variable {k : Type u} [Field k] (X : FScheme k) (hX : Properties X)

/-- The actual positive point line bundle has the original point-divisor class,
in every genus. -/
theorem positiveLineBundle_class_eq_pointDivisor
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hdim : topologicalKrullDim X.left ≤ 1) :
    letI := isIntegral_of_properties X hX
    letI := curveProperties_isNoetherian hX
    letI (x : ClosedPoint X.left) := isDiscreteValuationRing_stalk X hX x
    classOf X.left (positiveLineBundle X hX p hp) =
      DivisorClass.divisorToPicard X.left hdim (pointDivisor X p hp 1) := by
  let := isIntegral_of_properties X hX
  let := curveProperties_isNoetherian hX
  let (x : ClosedPoint X.left) := isDiscreteValuationRing_stalk X hX x
  exact idealDual_class_eq_point X.left (rationalPoint X p hp)
    (idealLineBundle X hX p hp).property hdim

end AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor
