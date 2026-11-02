/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.PointDivisor.IdealClass

/-! Interface examples and approved-foundation guards for the shared provider. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve

universe u
variable {k : Type u} [Field k] (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
  [∀ x : Scheme.ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk x.val)]

/-- The point class requires no curve compactification or chosen trivializing chart. -/
example (r : Scheme.RationalPoint k Y)
    (hI : IsLocallyRankOne Y (Scheme.Hom.idealModule r.sectionMap))
    (hdim : topologicalKrullDim Y ≤ 1) :
    classOf Y (dualLineBundle Y ⟨Scheme.Hom.idealModule r.sectionMap, hI⟩) =
      Picard.DivisorClass.divisorToPicard Y hdim
        (Finsupp.single (⟨r.point, r.point_isClosed⟩ : Scheme.ClosedPoint Y) 1) :=
  PointDivisor.idealDual_class_eq_point Y r hI hdim

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor.pointMapDivisor_eq_single' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor.pointMapDivisor_eq_single

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor.idealDual_class_eq_point' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor.idealDual_class_eq_point
