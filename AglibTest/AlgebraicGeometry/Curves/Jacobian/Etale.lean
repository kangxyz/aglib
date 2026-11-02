/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Etale

/-! # Invertible multiplication on the supplied Jacobian, with its native law -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group

universe u

variable {k : Type u} [Field k] {X : FScheme k} (hX : Curve.Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

example (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    Etale ((𝟙 (identityComponentOver P.obj)) ^ n).left :=
  Curve.etale_multiplication_identityComponentOver_of_isUnit hX P R n hn

example [IsAlgClosed k] [IsSeparated P.obj.hom] (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    IsFinite ((𝟙 (identityComponentOver P.obj)) ^ n).left ∧
      Etale ((𝟙 (identityComponentOver P.obj)) ^ n).left ∧
      Surjective ((𝟙 (identityComponentOver P.obj)) ^ n).left :=
  Curve.finite_etale_surjective_multiplication_identityComponentOver_of_isUnit hX P R n hn

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.etale_multiplication_identityComponentOver_of_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.etale_multiplication_identityComponentOver_of_isUnit

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.finite_etale_surjective_multiplication_identityComponentOver_of_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.finite_etale_surjective_multiplication_identityComponentOver_of_isUnit
