/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Dual
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Functoriality of the original dual and bidual

The contravariant functor uses the existing internal-Hom map and the
existing dual sheaves. Original bidual naturality is supplied separately
by BidualNaturality; no second dual construction is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible

variable (X : Scheme.{u})

/-- Equality of original internal-Hom sections is detected on every original component. -/
theorem section_ext {M N : X.Modules} {U : X.Opens}
    {s t : (sheaf X M N).val.obj (op U)}
    (h : ∀ (V : (Over U)ᵒᵖ) (m : M.val.obj (op V.unop.left)),
      s.val.app V m = t.val.app V m) : s = t := by
  apply Subtype.ext
  change (_ : RawHom X M N U) = _
  ext V m
  exact h V m

/-- Source-contravariance of the original internal Hom into the structure module. -/
def dualFunctor : X.Modulesᵒᵖ ⥤ X.Modules where
  obj M := dualSheaf X M.unop
  map f := _root_.SheafOfModules.InternalHom.map X.sheaf f.unop
    (𝟙 (SheafOfModules.unit X.ringCatSheaf))
  map_id M := _root_.SheafOfModules.InternalHom.map_id X.sheaf
  map_comp f g := by
    simpa only [Category.id_comp, unop_comp] using
      (_root_.SheafOfModules.InternalHom.map_comp X.sheaf f.unop
        (𝟙 (SheafOfModules.unit X.ringCatSheaf)) g.unop
        (𝟙 (SheafOfModules.unit X.ringCatSheaf))).symm

/-- The functor map is the original precomposition, on every original section. -/
theorem dualFunctor_map_apply {M N : X.Modulesᵒᵖ} (f : M ⟶ N)
    (U : X.Opens) (s : (dualSheaf X M.unop).val.obj (op U))
    (V : (Over U)ᵒᵖ) (m : N.unop.val.obj (op V.unop.left)) :
    (((dualFunctor X).map f).val.app (op U) s).val.app V m =
      s.val.app V (f.unop.val.app (op V.unop.left) m) := rfl

/-- The original contravariant dual functor is additive. -/
instance dualFunctor_additive : (dualFunctor X).Additive where
  map_add {M N} f g := by
    apply SheafOfModules.hom_ext
    ext U : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : RawHom X N.unop (SheafOfModules.unit X.ringCatSheaf) U.unop) = _
    ext V m
    change s.val.app V
      (f.unop.val.app (op V.unop.left) m + g.unop.val.app (op V.unop.left) m) = _
    exact (s.val.app V).hom.map_add _ _

end AlgebraicGeometry.Scheme.Modules.InternalHom
