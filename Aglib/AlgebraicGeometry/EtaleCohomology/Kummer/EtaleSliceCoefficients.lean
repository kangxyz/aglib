/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSliceTopology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients

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
      (gm X).over U :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun V => ((unitsSections U.left ((Scheme.Etale.sliceForward U).op.obj V)).trans
      (unitsSections X (op V.unop.left)).symm).toAddCommGrpIso)
    (by
      intro V W f
      ext a
      apply (unitsSections X (op W.unop.left)).injective
      change (unitsSections X (op W.unop.left))
        ((unitsSections X (op W.unop.left)).symm
          (unitsSections U.left ((Scheme.Etale.sliceForward U).op.obj W)
            ((gm U.left).obj.map ((Scheme.Etale.sliceForward U).op.map f) a))) =
        (unitsSections X (op W.unop.left) ((gm X).obj.map f.unop.left.op
          ((unitsSections X (op V.unop.left)).symm
            (unitsSections U.left ((Scheme.Etale.sliceForward U).op.obj V) a))))
      rw [AddEquiv.apply_symm_apply]
      change (unitsSections U.left ((Scheme.Etale.sliceForward U).op.obj W)
        ((gm U.left).obj.map ((Scheme.Etale.sliceForward U).op.map f) a)).toMul =
        (unitsSections X (op W.unop.left) ((gm X).obj.map f.unop.left.op
          ((unitsSections X (op V.unop.left)).symm
            (unitsSections U.left ((Scheme.Etale.sliceForward U).op.obj V) a)))).toMul
      rw [unitsSections_naturality, unitsSections_naturality,
        AddEquiv.apply_symm_apply]
      rfl))

end GroupCohomology.Kummer.Coefficients
