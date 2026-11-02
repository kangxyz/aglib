/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSliceTopology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.GlobalUnits

/-! # Original multiplicative coefficients on an etale slice

The actual small-etale slice equivalence identifies the original multiplicative
sheaf with its restriction. The comparison is the native global-units section
coordinate, and its naturality is the original units restriction formula.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme.EtaleCohomology

namespace GroupCohomology.Kummer.Coefficients

universe u

variable {X : Scheme.{u}} (U : X.Etale)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original units sheaf on a chart is the original units sheaf restricted
to the actual etale slice, not a separately chosen coefficient model. -/
def gmEtaleSliceIso :
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.obj (gm U.left) ≅
      (gm X).over U := by
  let eP := Functor.isoWhiskerLeft (Scheme.Etale.sliceForward U).op (gmGlobalUnitsIso U.left)
  let eQ := Functor.isoWhiskerLeft (Over.forget U).op (gmGlobalUnitsIso X)
  exact ObjectProperty.isoMk _ (eP ≪≫ eQ.symm)

/-- Whole global-units transport has the original forward section-coordinate value. -/
theorem gmEtaleSliceIso_hom_apply (V : (Over U)ᵒᵖ)
    (a : (gm U.left).obj.obj ((Scheme.Etale.sliceForward U).op.obj V)) :
    (gmEtaleSliceIso U).hom.hom.app V a =
      (unitsSections X (op V.unop.left)).symm
        (unitsSections U.left ((Scheme.Etale.sliceForward U).op.obj V) a) := rfl

end GroupCohomology.Kummer.Coefficients
