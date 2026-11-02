/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.ProjectivityField

/-!
# Consumer checks for the same Jacobian over an arbitrary field

The quasi-projectivity supplier needs no separatedness; properness and projectivity retain the
original separated, locally finite-type Picard representative. No algebraic closedness is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

namespace AglibTest.CurvesJacobianProjectivityField

variable {k : Type u} [Field k] {X : FScheme k} (hX : Curve.Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include hX in
example :
    letI := picardCommGrpObj X.hom P R
    IsHQuasiProjective (identityComponentOver P.obj).hom :=
  isHQuasiProjective_identityComponentOver hX P R

include hX in
example [IsSeparated P.obj.hom] :
    letI := picardCommGrpObj X.hom P R
    IsProper (identityComponentOver P.obj).hom ∧ IsHProjective (identityComponentOver P.obj).hom :=
  ⟨isProper_identityComponentOver hX P R, isHProjective_identityComponentOver hX P R⟩

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isHQuasiProjective_identityComponentOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isHQuasiProjective_identityComponentOver

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isProper_identityComponentOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isProper_identityComponentOver

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isHProjective_identityComponentOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isHProjective_identityComponentOver

end AglibTest.CurvesJacobianProjectivityField
