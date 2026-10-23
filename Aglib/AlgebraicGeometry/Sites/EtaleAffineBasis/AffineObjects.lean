/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.Restriction

/-!
# Affine models of original small étale objects

An affine object in the original small étale site has a native affine-site
model isomorphic to it over the base. This bridges the affine components of a
qcqs hypercover with literal affine-site restriction evaluations.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

/-- The native affine étale model of an affine original small-site object. -/
def affineModel {S : Scheme.{u}} (U : S.Etale) [IsAffine U.left] : S.AffineEtale :=
  Scheme.AffineEtale.mk (U.left.isoSpec.inv ≫ U.hom)

/-- The affine model is isomorphic to the original object over the same base. -/
def affineModelIso {S : Scheme.{u}} (U : S.Etale) [IsAffine U.left] :
    (Scheme.AffineEtale.Spec S).obj (affineModel U) ≅ U :=
  MorphismProperty.Over.isoMk U.left.isoSpec.symm

/-- The affine model comparison identifies restriction evaluation with original
small-site evaluation, without changing the coefficient universe. -/
def affineModelEvaluationIso {S : Scheme.{u}} (U : S.Etale) [IsAffine U.left]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((abelianRestriction S).obj F).obj.obj (op (affineModel U)) ≅ F.obj.obj (op U) :=
  F.obj.mapIso (affineModelIso U).op.symm

end AlgebraicGeometry.Scheme.EtaleAffineBasis
