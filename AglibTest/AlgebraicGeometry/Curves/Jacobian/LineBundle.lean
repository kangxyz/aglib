/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.LineBundle

/-! Native cube and line-bundle pullback on the same Picard representative's
actual identity component. -/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open Scheme.OverField Scheme.OverField.Curve Scheme.RelativePicard Scheme.Group
open Scheme.Modules.Invertible
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : Scheme.LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((Scheme.locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include hX

example :
    letI := picardCommGrpObj X.hom P R
    ∀ {T : Over (Spec (.of k))} (f g h : T ⟶ identityComponentOver P.obj)
      (a : PicardGroup (identityComponentOver P.obj).left),
      LineBundleCube.cubeClass f g h a = 0 :=
  cubeClass_identityComponentOver hX P R

example :
    letI := picardCommGrpObj X.hom P R
    ∀ (a : PicardGroup (identityComponentOver P.obj).left) (n : ℕ),
      pullbackClass ((𝟙 (identityComponentOver P.obj)) ^ n).left a =
        (n * (n + 1) / 2) • a + (n * (n - 1) / 2) •
          pullbackClass ((𝟙 (identityComponentOver P.obj))⁻¹).left a :=
  pullbackClass_multiplication_identityComponentOver hX P R

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.cubeClass_identityComponentOver' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cubeClass_identityComponentOver

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.pullbackClass_multiplication_identityComponentOver' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pullbackClass_multiplication_identityComponentOver

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.nonempty_multiplicationPullbackIso_identityComponentOver_of_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nonempty_multiplicationPullbackIso_identityComponentOver_of_symmetric
