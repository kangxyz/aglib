/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.IdentityComponent

/-!
# Consumer checks for `Aglib.AlgebraicGeometry.Curves.Jacobian.IdentityComponent`

The identity component of the Picard scheme of a curve equals any open and closed degree-zero set
containing the unit, is the image of the Abel morphism and is proper; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

universe u

namespace AglibTest.CurvesJacobianIdentityComponent

variable {k : Type u} [Field k] {X : FScheme k}

/-- A curve over an algebraically closed field has a rational point. -/
example [IsAlgClosed k] (hX : Curve.Properties X) :
    ∃ o : Spec (.of k) ⟶ X.left, o ≫ X.hom = 𝟙 _ :=
  hX.exists_rationalPoint_of_isAlgClosed

/-- Properness of the identity component from a degree-zero clopen set. -/
example [IsAlgClosed k] (hX : Curve.Properties X) (P : LocallyNoetherianOver (Spec (.of k)))
    [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom] (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (Z : Set P.obj.left) (hZ : IsClopen Z)
    (hZ₁ : (letI := picardCommGrpObj X.hom P R; Group.unitPoint P.obj) ∈ Z)
    (hZdeg : ∀ L : PicardGroup X.left, (picardPoint P R L).left (IsLocalRing.closedPoint k) ∈ Z →
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX L = 0) :
    letI := picardCommGrpObj X.hom P R
    IsProper (identityComponentOver P.obj).hom :=
  isProper_identityComponentOver_of_isClopen_of_isAlgClosed hX P R Z hZ hZ₁ hZdeg

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Properties.exists_rationalPoint_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Properties.exists_rationalPoint_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.exists_comp_abelMorphism_eq_picardPoint_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.exists_comp_abelMorphism_eq_picardPoint_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.exists_picardPoint_eq_of_isClosed_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.exists_picardPoint_eq_of_isClosed_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.range_abelMorphism_eq_and_identityComponent_eq_of_isClopen_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.range_abelMorphism_eq_and_identityComponent_eq_of_isClopen_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.identityComponent_eq_of_isClopen_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.identityComponent_eq_of_isClopen_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_mem_identityComponent_iff_of_isClopen_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_mem_identityComponent_iff_of_isClopen_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isProper_identityComponentOver_of_isClopen_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isProper_identityComponentOver_of_isClopen_of_isAlgClosed

end AglibTest.CurvesJacobianIdentityComponent

