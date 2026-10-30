/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Dimension

/-! # The original representative and arbitrary-field Jacobian dimension interface -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group

universe u

variable {k : Type u} [Field k] {X : FScheme k} (hX : Curve.Properties X)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

example [LocallyOfFiniteType P.obj.hom] :
    letI := picardCommGrpObj X.hom P R
    SmoothOfRelativeDimension (Curve.coherentGenus k X) (identityComponentOver P.obj).hom :=
  Curve.smoothOfRelativeDimension_identityComponentOver hX P R

example [LocallyOfFiniteType P.obj.hom] :
    letI := picardCommGrpObj X.hom P R
    topologicalKrullDim (identityComponentOver P.obj).left = Curve.coherentGenus k X :=
  Curve.topologicalKrullDim_identityComponentOver_eq_coherentGenus hX P R

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.topologicalKrullDim_identityComponentOver_eq_coherentGenus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.topologicalKrullDim_identityComponentOver_eq_coherentGenus
