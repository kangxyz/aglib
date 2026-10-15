/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic

/-!
# Presentation transport from affine charts

An actual affine-chart presentation transports to the over-site of the
corresponding open. Its finite index sets are retained. No Noetherian
hypothesis or coherent category is required.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Transfer a presentation on an affine chart to the actual over-site of
that affine open in the original scheme. -/
def affinePresentationToOver {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (P : (M.restrict U.2.fromSpec).Presentation) : (M.over U.1).Presentation := by
  let e := U.2.isoSpec
  let P' := Scheme.Modules.presentationRestrict e.hom P
  let i : (M.restrict U.2.fromSpec).restrict e.hom ≅ M.restrict U.1.ι :=
    ((Scheme.Modules.restrictFunctorComp e.hom U.2.fromSpec).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr U.2.isoSpec_hom_fromSpec).app M
  let Q := P'.ofIsIso i.hom
  let E := Scheme.Modules.overEquiv U.1
  let e' : E.inverse.obj (M.restrict U.1.ι) ≅ M.over U.1 :=
    (E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U.1).app M)).symm ≪≫
      (E.unitIso.app (M.over U.1)).symm
  exact (Q.map E.inverse
    (U.1.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofIsIso e'.hom

instance affinePresentationToOver_isFinite {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (P : (M.restrict U.2.fromSpec).Presentation) [P.IsFinite] :
    (affinePresentationToOver M U P).IsFinite := by
  dsimp [affinePresentationToOver, Scheme.Modules.presentationRestrict]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
