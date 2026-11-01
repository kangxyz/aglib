/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.GenusZero

/-! # Same-representative genus-zero Jacobian over an arbitrary field -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Scheme Scheme.OverField Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] {X : FScheme k} (hX : Curve.Properties X)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom]

example (hg : Curve.coherentGenus k X = 0) :
    letI := picardCommGrpObj X.hom P R
    (identityComponentOver P.obj).hom ≫ η[identityComponentOver P.obj].left = 𝟙 _ :=
  Curve.identityComponentOver_hom_comp_one_of_genus_zero hX P R hg

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.identityComponentIsoSpecOfGenusZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.identityComponentIsoSpecOfGenusZero
