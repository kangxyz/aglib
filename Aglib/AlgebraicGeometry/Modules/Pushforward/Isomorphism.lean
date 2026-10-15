/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
/-! # Direct image along scheme isomorphisms

The actual module-sheaf pushforward along an isomorphism agrees naturally
with restriction along its inverse, including the structure-sheaf action.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Direct image along a scheme isomorphism is actual restriction along its
inverse. This comparison includes the structure-sheaf module actions. -/
def pushforwardIsoRestrict {Z X : Scheme.{u}} (e : Z ≅ X) :
    pushforward e.hom ≅ restrictFunctor e.inv :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (pushforward e.hom) (restrictFunctorAdjCounitIso e.inv).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (pushforwardComp e.hom e.inv ≪≫ pushforwardCongr e.hom_inv_id ≪≫
        pushforwardId Z) _ ≪≫
    Functor.leftUnitor _

end AlgebraicGeometry.Scheme.Modules
