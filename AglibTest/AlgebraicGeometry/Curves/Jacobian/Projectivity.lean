/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Projectivity

/-!
# Consumer checks for projectivity of the actual Jacobian

For any supplied locally Noetherian fppf Picard representative over an algebraically closed
field, its same identity component is H-projective. No replacement Picard scheme is an input.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

namespace AglibTest.CurvesJacobianProjectivity

example {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k}
    (hX : Curve.Properties X) (P : LocallyNoetherianOver (Spec (.of k)))
    [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) :
    letI := picardCommGrpObj X.hom P R
    IsHProjective (identityComponentOver P.obj).hom :=
  isHProjective_identityComponentOver_of_isAlgClosed hX P R

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isHQuasiProjective_identityComponentOver_of_isAlgClosed_of_closedImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isHQuasiProjective_identityComponentOver_of_isAlgClosed_of_closedImmersion

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isHQuasiProjective_identityComponentOver_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isHQuasiProjective_identityComponentOver_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isHProjective_identityComponentOver_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isHProjective_identityComponentOver_of_isAlgClosed

end AglibTest.CurvesJacobianProjectivity
