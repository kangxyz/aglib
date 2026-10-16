/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic

/-!
# Comparison with the canonical specialized tensor sheaf

Both interfaces use the actual presheaf module tensor followed by module
sheafification. The object, map and forward braiding comparisons below retain
those original maps; no local freeness premise is introduced.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace AlgebraicGeometry.Scheme.Modules

lemma tensorLeftFunctor_obj_eq_tensorSheaf (X : Scheme.{u}) (M N : X.Modules) :
    (SheafOfModulesOfCommRing.tensorLeftFunctor X.sheaf M).obj N =
      _root_.AlgebraicGeometry.Scheme.Modules.tensorSheaf X M N := rfl

lemma tensorMap_eq_tensorSheafMap (X : Scheme.{u}) {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    (SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).map f ⊗ₘ
        (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map g) =
      _root_.AlgebraicGeometry.Scheme.Modules.tensorSheafMap X f g := rfl

lemma tensorBraiding_eq_tensorSheafBraiding (X : Scheme.{u}) (M N : X.Modules) :
    SheafOfModulesOfCommRing.tensorBraiding X.sheaf M N =
      _root_.AlgebraicGeometry.Scheme.Modules.tensorSheafBraiding X M N := rfl

end AlgebraicGeometry.Scheme.Modules
