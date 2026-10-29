/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeStrata

/-!
# Consumer checks for `Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeStrata`

Riemann–Roch in Euler-characteristic form and the identification of the Hilbert-polynomial strata of
the Picard scheme of an embedded curve with the degree strata; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

universe u

namespace AglibTest.CurvesJacobianDegreeStrata

variable {k : Type u} [Field k] {ι : Type u} {Y : Scheme.{u}}
  (i : Y ⟶ AlgebraicGeometry.ProjectiveSpace k ι) [IsClosedImmersion i] {N : ℕ}
  (e : ι ≃ Fin (N + 1)) [Flat (i ≫ AlgebraicGeometry.ProjectiveSpace.toSpec k ι)]

/-- Riemann–Roch: `χ(X, L) = deg L + 1 - g`. -/
example {X : FScheme k} (hX : Curve.Properties X) (L : LineBundle X.left) :
    Cohomology.moduleEulerChar X.hom L.val =
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX (classOf X.left L) + 1 - coherentGenus k X :=
  moduleEulerChar_eq_curveDegree_add_one_sub_genus X hX L

/-- The rational point of a class lies in the stratum of `m ↦ m · deg O(1) + 1 - g - d` if and
only if the class has degree `d`. -/
example (hX : Curve.Properties (Over.mk (i ≫ AlgebraicGeometry.ProjectiveSpace.toSpec k ι) :
      FScheme k))
    (P : LocallyNoetherianOver (Spec (.of k)))
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf (i ≫ AlgebraicGeometry.ProjectiveSpace.toSpec k ι)).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (c : PicardGroup Y) (d : ℤ) :
    (picardPoint (X := Over.mk (i ≫ AlgebraicGeometry.ProjectiveSpace.toSpec k ι)) P R c).left
        (IsLocalRing.closedPoint k) ∈
        (Strata.eulerCondition i N e (degreeStratumPolynomial i hX d)).opens (T := P.obj)
          (R.homEquiv (𝟙 P)) ↔
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        (Over.mk (i ≫ AlgebraicGeometry.ProjectiveSpace.toSpec k ι)) hX c = d :=
  picardPoint_mem_opens_eulerCondition_degreeStratumPolynomial_iff i e P R hX c d

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.moduleCohomologyDimension_eq_finrank_moduleCohomology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.moduleCohomologyDimension_eq_finrank_moduleCohomology

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.moduleCohomologyDimension_eq_zero_of_two_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.moduleCohomologyDimension_eq_zero_of_two_le

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.moduleEulerChar_eq_curveDegree_add_one_sub_genus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.moduleEulerChar_eq_curveDegree_add_one_sub_genus

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.fiberDualTwistEulerChar_closedPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.fiberDualTwistEulerChar_closedPoint

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.rationalFiber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.rationalFiber

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.rationalFiberIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.rationalFiberIso

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.properties_rationalFiber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.properties_rationalFiber

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.degreeStratumPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.degreeStratumPolynomial

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.fiberDualTwistEulerChar_closedPoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.fiberDualTwistEulerChar_closedPoint_eq

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_mem_opens_eulerCondition_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_mem_opens_eulerCondition_iff

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_mem_opens_eulerCondition_iff_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_mem_opens_eulerCondition_iff_eval

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_mem_opens_eulerCondition_degreeStratumPolynomial_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_mem_opens_eulerCondition_degreeStratumPolynomial_iff

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isClopen_opens_eulerCondition_degreeStratumPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isClopen_opens_eulerCondition_degreeStratumPolynomial

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.unitPoint_mem_opens_eulerCondition_degreeStratumPolynomial_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.unitPoint_mem_opens_eulerCondition_degreeStratumPolynomial_zero

end AglibTest.CurvesJacobianDegreeStrata

