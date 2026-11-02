/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Smooth

/-! # Smoothness and geometric integrality of the original representative -/

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

example : Smooth P.obj.hom := Curve.smooth_picardRepresentative hX P R

example [LocallyOfFiniteType P.obj.hom] :
    letI := picardCommGrpObj X.hom P R
    GeometricallyIntegral (identityComponentOver P.obj).hom :=
  Curve.geometricallyIntegral_identityComponentOver hX P R
