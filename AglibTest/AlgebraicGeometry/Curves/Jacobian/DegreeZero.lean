/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeZero

/-!
# Consumer checks for `Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeZero`

The Jacobian of a smooth proper curve over an algebraically closed field: the identity component of
the Picard scheme is proper, is the image of the Abel morphism and the degree-zero stratum, and its
rational points are the degree-zero classes; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

universe u

namespace AglibTest.CurvesJacobianDegreeZero

variable {k : Type u} [Field k] {X : FScheme k}

/-- The Jacobian: `J` proper, rational points of degree zero, and the image of the Abel morphism,
from `Curve.Properties X` and algebraic closedness only. -/
example [IsAlgClosed k] (hX : Curve.Properties X) :
    ∃ (P : LocallyNoetherianOver (Spec (.of k)))
      (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (_ : LocallyOfFiniteType P.obj.hom) (_ : IsSeparated P.obj.hom),
      (letI := picardCommGrpObj X.hom P R; IsProper (identityComponentOver P.obj).hom) := by
  obtain ⟨P, R, h, hs, hJ, -, -⟩ :=
    exists_representableBy_fppfPicardSheaf_isProper_identityComponentOver_of_isAlgClosed hX
  exact ⟨P, R, h, hs, hJ⟩

/-- For any representation, a rational point of the identity component is a degree-zero class. -/
example [IsAlgClosed k] (hX : Curve.Properties X) (P : LocallyNoetherianOver (Spec (.of k)))
    [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom] (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (L : PicardGroup X.left) :
    letI := picardCommGrpObj X.hom P R
    (picardPoint P R L).left (IsLocalRing.closedPoint k) ∈ identityComponent P.obj ↔
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX L = 0 :=
  picardPoint_mem_identityComponent_iff_of_isAlgClosed hX P R L

open scoped CategoryTheory.MonObj in
/-- The rational points of the Jacobian are the degree-zero classes, as groups. -/
example [IsAlgClosed k] (hX : Curve.Properties X) (P : LocallyNoetherianOver (Spec (.of k)))
    [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom] (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) :
    letI := picardCommGrpObj X.hom P R
    (curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX).ker ≃+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj) :=
  degreeZeroAddEquivOfIsAlgClosed hX P R

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.identityComponent_eq_opens_eulerCondition_degreeStratumPolynomial_zero_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.identityComponent_eq_opens_eulerCondition_degreeStratumPolynomial_zero_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.exists_isClopen_degreeZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.exists_isClopen_degreeZero

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.range_abelMorphism_eq_identityComponent_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.range_abelMorphism_eq_identityComponent_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_mem_identityComponent_iff_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_mem_identityComponent_iff_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isProper_identityComponentOver_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isProper_identityComponentOver_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.exists_representableBy_fppfPicardSheaf_isProper_identityComponentOver_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.exists_representableBy_fppfPicardSheaf_isProper_identityComponentOver_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.degreeZeroAddEquivOfIsAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.degreeZeroAddEquivOfIsAlgClosed

end AglibTest.CurvesJacobianDegreeZero

