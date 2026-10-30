/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Finite
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Etale
public import Aglib.AlgebraicGeometry.Curves.Jacobian.ProjectivityField

/-!
# Positive multiplication on the original Jacobian over any field

The same supplied Picard representative has a smooth, geometrically integral,
H-projective identity component over the original field. General positive
multiplication is therefore finite, flat and surjective, including inseparable
levels. At an invertible level the existing differential criterion also gives
etaleness of this original multiplication morphism.
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
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include hX in
/-- Positive multiplication on the same Jacobian is finite, flat and surjective
over every field. No condition on the characteristic is required. -/
theorem finite_flat_surjective_multiplication_identityComponentOver_of_pos
    (n : ℕ) (hn : 0 < n) :
    letI := picardCommGrpObj X.hom P R
    IsFinite ((𝟙 (identityComponentOver P.obj)) ^ n).left ∧
      Flat ((𝟙 (identityComponentOver P.obj)) ^ n).left ∧
      Surjective ((𝟙 (identityComponentOver P.obj)) ^ n).left := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  exact Multiplication.multiplication_finite_flat_surjective_of_isHProjective
    (Grp.mk (identityComponentOver P.obj)) n hn

include hX in
/-- Invertible multiplication on the original Jacobian is finite etale and
surjective over every field. -/
theorem finite_etale_surjective_multiplication_identityComponentOver
    (n : ℕ) (hn : IsUnit (n : k)) :
    letI := picardCommGrpObj X.hom P R
    IsFinite ((𝟙 (identityComponentOver P.obj)) ^ n).left ∧
      Etale ((𝟙 (identityComponentOver P.obj)) ^ n).left ∧
      Surjective ((𝟙 (identityComponentOver P.obj)) ^ n).left := by
  let := picardCommGrpObj X.hom P R
  obtain ⟨hfinite, _, hsurj⟩ :=
    finite_flat_surjective_multiplication_identityComponentOver_of_pos hX P R n
      (Nat.pos_of_ne_zero fun h => by simp [h] at hn)
  exact ⟨hfinite, etale_multiplication_identityComponentOver_of_isUnit hX P R n hn, hsurj⟩

end AlgebraicGeometry.Scheme.OverField.Curve
