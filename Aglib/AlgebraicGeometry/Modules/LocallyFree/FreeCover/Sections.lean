/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FreeCover
/-!
# Original sections of a free presentation on an open

The existing transport from a free restriction to its over-site presentation
preserves the original free sections. The equation uses the original
`overEquivalence` object and the original components of the supplied frame.
The scheme, open, index type and module sheaf are arbitrary.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} {I : Type u} {M : X.Modules}

/-- The original over-site free section is sent to the original supplied frame section. -/
theorem freeIsoOverOfRestrictFreeIso_hom_freeSection (U : X.Opens)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅ M.restrict U.ι)
    (i : I) (W : U.toScheme.Opens) :
    (freeIsoOverOfRestrictFreeIso U e).hom.val.app (op (U.overEquivalence.inverse.obj W))
      ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).val
        (op (U.overEquivalence.inverse.obj W))) =
      e.hom.val.app (op W)
        ((SheafOfModules.freeSection (R := U.toScheme.ringCatSheaf) i).val (op W)) := by
  let F := (Scheme.Modules.overEquiv U).functor
  let η : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm
  let a := SheafOfModules.mapFreeIso F I η
  let f := (freeIsoOverOfRestrictFreeIso U e).hom
  let c := (Scheme.Modules.overFunctorEquiv U).app M
  have hf : F.map f = a.inv ≫ e.hom ≫ c.inv :=
    (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.map_preimage _
  have H : a.hom ≫ F.map f ≫ c.hom = e.hom := by
    rw [hf]
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have ha := congrArg (fun φ => φ.val.app (op W) (1 : Γ(U.toScheme, W)))
    (SheafOfModules.ιFree_mapFreeIso_hom F I η i)
  change a.hom.val.app (op W)
      ((SheafOfModules.freeSection (R := U.toScheme.ringCatSheaf) i).val (op W)) =
    (SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).val
      (op (U.overEquivalence.inverse.obj W)) at ha
  have H' := congrArg (fun φ => φ.val.app (op W)
    ((SheafOfModules.freeSection (R := U.toScheme.ringCatSheaf) i).val (op W))) H
  change f.val.app (op (U.overEquivalence.inverse.obj W))
    (a.hom.val.app (op W)
      ((SheafOfModules.freeSection (R := U.toScheme.ringCatSheaf) i).val (op W))) =
    e.hom.val.app (op W)
      ((SheafOfModules.freeSection (R := U.toScheme.ringCatSheaf) i).val (op W)) at H'
  rw [ha] at H'
  exact H'

end AlgebraicGeometry.Scheme.Modules
