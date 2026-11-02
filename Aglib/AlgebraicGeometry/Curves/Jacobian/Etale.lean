/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Dimension
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Multiplication
public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Commutative
public import Aglib.AlgebraicGeometry.Group.MultiplicationSmoothEtale

/-!
# Invertible multiplication on the original Jacobian is finite etale

Smoothness and the native differential prove etaleness over every field.
Over an algebraically closed field, the existing A4 finiteness and surjectivity
theorems give finite etale surjective multiplication on this same identity
component. The existing A4 etale-finiteness dependency is retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include hX in
/-- Multiplication by an invertible natural scalar on the original Jacobian
is etale over the original arbitrary field. -/
theorem etale_multiplication_identityComponentOver_of_isUnit
    (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    Etale ((𝟙 (identityComponentOver P.obj)) ^ n).left := by
  let := picardCommGrpObj X.hom P R
  let := smooth_identityComponentOver hX P R
  exact Multiplication.multiplication_etale_of_smooth_of_isUnit
    (Grp.mk (identityComponentOver P.obj)) n hn

include hX in
/-- The existing finite surjective multiplication theorem, together with the
smooth differential criterion, gives finite etale surjective multiplication
on the same Jacobian over an algebraically closed field. -/
theorem finite_etale_surjective_multiplication_identityComponentOver_of_isUnit
    [IsAlgClosed k] [IsSeparated P.obj.hom] (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    IsFinite ((𝟙 (identityComponentOver P.obj)) ^ n).left ∧
      Etale ((𝟙 (identityComponentOver P.obj)) ^ n).left ∧
      Surjective ((𝟙 (identityComponentOver P.obj)) ^ n).left := by
  let := picardCommGrpObj X.hom P R
  exact ⟨isFinite_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn,
    etale_multiplication_identityComponentOver_of_isUnit hX P R n hn,
    surjective_multiplication_identityComponentOver_of_isUnit_of_isAlgClosed hX P R n hn⟩

end AlgebraicGeometry.Scheme.OverField.Curve
