/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Dual

/-! # Canonical evaluation into the original double dual

Evaluation and its section laws apply to every module sheaf, without rank hypotheses.
The implementation and qualified declarations are retained from the line-bundle interface.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable (X : Scheme.{u}) (M : SheafOfModules.{u} X.ringCatSheaf)

/-- Evaluation by a section, on every smaller open. -/
def bidualSection (U : X.Opens) (m : M.val.obj (op U)) :
    (dualSheaf X (dualSheaf X M)).val.obj (op U) :=
  ⟨{
    app V := AddCommGrpCat.ofHom {
      toFun ell := ell.val.app (op (Over.mk (𝟙 V.unop.left)))
        (M.val.map V.unop.hom.op m)
      map_zero' := rfl
      map_add' ell ell' := rfl }
    naturality {V W} i := by
      ext ell
      change ell.val.app (op (Over.mk i.unop.left)) (M.val.map W.unop.hom.op m) =
        X.presheaf.map i.unop.left.op
          (ell.val.app (op (Over.mk (𝟙 V.unop.left))) (M.val.map V.unop.hom.op m))
      have hn := NatTrans.naturality_apply ell.val
        (Over.homMk i.unop.left : Over.mk i.unop.left ⟶
          Over.mk (𝟙 V.unop.left)).op (M.val.map V.unop.hom.op m)
      change ell.val.app (op (Over.mk i.unop.left))
          (M.val.map i.unop.left.op (M.val.map V.unop.hom.op m)) = _ at hn
      rw [← M.val.map_comp_apply, ← op_comp, Over.w i.unop] at hn
      exact hn
  }, by
    intro V r ell
    change X.presheaf.map (𝟙 V.unop.left).op r •
      (show Γ(X, V.unop.left) from ell.val.app (op (Over.mk (𝟙 V.unop.left)))
        (M.val.map V.unop.hom.op m)) = _
    simp⟩

/-- The original evaluation section is additive. -/
theorem bidualSection_add (U : X.Opens) (m n : M.val.obj (op U)) :
    bidualSection X M U (m + n) = bidualSection X M U m + bidualSection X M U n := by
  apply Subtype.ext
  change (_ : InternalHom.RawHom X (dualSheaf X M)
    (SheafOfModules.unit X.ringCatSheaf) U) = _
  ext V ell
  change ell.val.app (op (Over.mk (𝟙 V.unop.left))) (M.val.map V.unop.hom.op (m + n)) = _
  rw [map_add, map_add]
  rfl

/-- The original evaluation section preserves its actual local scalar action. -/
theorem bidualSection_smul (U : X.Opens) (r : Γ(X, U)) (m : M.val.obj (op U)) :
    bidualSection X M U (r • m) = r • bidualSection X M U m := by
  apply Subtype.ext
  change (_ : InternalHom.RawHom X (dualSheaf X M)
    (SheafOfModules.unit X.ringCatSheaf) U) = _
  ext V ell
  change ell.val.app (op (Over.mk (𝟙 V.unop.left)))
      (M.val.map V.unop.hom.op (r • m)) =
    X.presheaf.map V.unop.hom.op r •
      (show Γ(X, V.unop.left) from ell.val.app (op (Over.mk (𝟙 V.unop.left)))
        (M.val.map V.unop.hom.op m))
  rw [M.val.map_smul]
  exact ell.property _ _ _

/-- Restriction of the original evaluation section is evaluation of the restriction. -/
theorem bidualSection_restrict {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (m : M.val.obj U) :
    bidualSection X M V.unop (M.val.map i m) =
      (dualSheaf X (dualSheaf X M)).val.map i (bidualSection X M U.unop m) := by
  apply Subtype.ext
  change (_ : InternalHom.RawHom X (dualSheaf X M)
    (SheafOfModules.unit X.ringCatSheaf) V.unop) = _
  ext W ell
  change ell.val.app (op (Over.mk (𝟙 W.unop.left))) (M.val.map W.unop.hom.op (M.val.map i m)) =
    ell.val.app (op (Over.mk (𝟙 W.unop.left))) (M.val.map (W.unop.hom ≫ i.unop).op m)
  rw [← M.val.map_comp_apply, op_comp]
  rfl

/-- The canonical evaluation morphism to the actual double dual. -/
def bidualMap : M ⟶ dualSheaf X (dualSheaf X M) where
  val.app U := ModuleCat.ofHom {
    toFun m := bidualSection X M U.unop m
    map_add' := bidualSection_add X M U.unop
    map_smul' := bidualSection_smul X M U.unop }
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact bidualSection_restrict X M i

/-- The defining formula is literally evaluation, with restriction to the chosen open. -/
-- Keep bidual evaluation; simpNF only unfolds the implicit open-restriction component types.
@[nolint simpNF, simp] theorem bidualMap_apply (U : X.Opens) (m : M.val.obj (op U))
    (V : (Over U)ᵒᵖ) (ell : (dualSheaf X M).val.obj (op V.unop.left)) :
    ((bidualMap X M).val.app (op U) m).val.app V ell =
      ell.val.app (op (Over.mk (𝟙 V.unop.left))) (M.val.map V.unop.hom.op m) := rfl

theorem bidualMap_evaluate (U : X.Opens) (m : M.val.obj (op U))
    (ell : (dualSheaf X M).val.obj (op U)) :
    ((bidualMap X M).val.app (op U) m).val.app (op (Over.mk (𝟙 U))) ell =
      ell.val.app (op (Over.mk (𝟙 U))) m := by
  rw [bidualMap_apply]
  congr 1
  change M.val.presheaf.map (𝟙 (op U)) m = m
  exact ConcreteCategory.congr_hom (M.val.presheaf.map_id (op U)) m

end AlgebraicGeometry.Scheme.Modules.Invertible
