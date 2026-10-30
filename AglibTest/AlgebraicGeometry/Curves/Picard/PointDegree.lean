/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.PointDegree

/-! Pure degree interfaces, without a Jacobian divisibility import. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
variable {k : Type u} [Field k] {X : FScheme k} (hX : Curve.Properties X)

/-- Point degree does not require algebraically closed constants. -/
example (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    Curve.curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension
      Curve.Picard.Degree.properCurveProductFormula X hX
      (classOf X.left (Curve.PointDivisor.positiveLineBundle X hX p hp)) = 1 :=
  Curve.curveDegree_positiveLineBundle hX p hp

/-- Modulo-degree surjectivity needs no divisibility assertion or selected point. -/
example [IsAlgClosed k] (n : ℕ) : Function.Surjective (Curve.curveDegreeMod hX n) :=
  Curve.curveDegreeMod_surjective_of_isAlgClosed hX n

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.curveDegree_positiveLineBundle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.curveDegree_positiveLineBundle

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.curveDegree_surjective_of_isAlgClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.curveDegree_surjective_of_isAlgClosed

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.curveDegreeMod' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.curveDegreeMod

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.curveDegreeMod_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.curveDegreeMod_apply

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.curveDegreeMod_surjective_of_isAlgClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.curveDegreeMod_surjective_of_isAlgClosed
