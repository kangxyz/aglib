/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Bidual
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.BidualNaturality
public import Aglib.AlgebraicGeometry.Modules.InternalHom.DualFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Naturality of original bidual evaluation

The contravariant functor uses the existing internal-Hom map. Its objects
are the existing dual sheaves, and canonical biduality retains evaluation.
No second dual or evaluation construction is introduced.
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

/-- The complete original functor-map equation, without nested functor conversion. -/
theorem dualFunctor_map_eq {M N : X.Modulesᵒᵖ} (f : M ⟶ N) :
    (dualFunctor X).map f = _root_.SheafOfModules.InternalHom.map X.sheaf f.unop
      (𝟙 (SheafOfModules.unit X.ringCatSheaf)) := rfl

/-- Naturality written entirely through the original ringed-site map constructor. -/
theorem bidualMap_naturality_raw {M N : X.Modules} (f : M ⟶ N) :
    f ≫ bidualMap X N = bidualMap X M ≫
      _root_.SheafOfModules.InternalHom.map X.sheaf
        (_root_.SheafOfModules.InternalHom.map X.sheaf f
          (𝟙 (SheafOfModules.unit X.ringCatSheaf)))
        (𝟙 (SheafOfModules.unit X.ringCatSheaf)) := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  change (_ : RawHom X (dualSheaf X N)
    (SheafOfModules.unit X.ringCatSheaf) U.unop) = _
  ext V ell
  have h₁ := bidualMap_apply X N U.unop (f.val.app U m) V ell
  have h₂ := _root_.SheafOfModules.InternalHom.map_apply X.sheaf
    (_root_.SheafOfModules.InternalHom.map X.sheaf f
      (𝟙 (SheafOfModules.unit X.ringCatSheaf)))
    (𝟙 (SheafOfModules.unit X.ringCatSheaf)) U.unop
    ((bidualMap X M).val.app U m) V ell
  have h₃ := bidualMap_apply X M U.unop m V
    ((_root_.SheafOfModules.InternalHom.map X.sheaf f
      (𝟙 (SheafOfModules.unit X.ringCatSheaf))).val.app (op V.unop.left) ell)
  have h₄ := _root_.SheafOfModules.InternalHom.map_apply X.sheaf f
    (𝟙 (SheafOfModules.unit X.ringCatSheaf)) V.unop.left ell
    (op (Over.mk (𝟙 V.unop.left))) (M.val.map V.unop.hom.op m)
  have hn := congrArg (fun n => ell.val.app (op (Over.mk (𝟙 V.unop.left))) n)
    (ConcreteCategory.congr_hom (f.val.naturality V.unop.hom.op) m).symm
  exact h₁.trans (hn.trans (h₄.symm.trans (h₃.symm.trans h₂.symm)))

end AlgebraicGeometry.Scheme.Modules.InternalHom
