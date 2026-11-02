/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.IdentityComponent

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.Cohomology

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] (X : FScheme k)
    [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
      (fppfPicardSheaf X.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) :
    letI := picardCommGrpObj X.hom P R
    Module.finrank k (Cotangent.Space η[identityComponentOver P.obj]) =
      Module.finrank k (structureCohomology k X 1) :=
  finrank_identityComponentCotangent_eq_structureH1 X P R
