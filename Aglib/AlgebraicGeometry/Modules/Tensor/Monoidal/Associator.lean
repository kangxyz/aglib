/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.Associator
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.LocalIso

/-!
# The general associator of scheme-module tensors

Let `presheafLocalIso X` be the class of maps of module presheaves over the structure sheaf of a
scheme `X` that become isomorphisms after module sheafification. It is monoidal
(`presheafLocalIso_isMonoidal`), so for arbitrary module sheaves `M N O` the sheafified whiskered
units `L (η ▷ O)` and `L (M ◁ η)` are isomorphisms, and `tensorSheafAssociator X M N O` is the
sheafified presheaf associator conjugated by them:
`tensorSheaf X (tensorSheaf X M N) O ≅ tensorSheaf X M (tensorSheaf X N O)`.

No line-bundle, local-freeness or finiteness hypothesis is used. Besides the defining square, the
associator is described on underlying presheaves through the sheafification units and on pure
section tensors (`tensorSheafAssociator_hom_tmul`, `tensorSheafAssociator_inv_tmul`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

local notation "𝓛" => SheafOfModulesOfCommRing.associatedSheaf X.sheaf
local notation "𝓖" => SheafOfModulesOfCommRing.toPresheaf X.sheaf
local notation "η" => SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf

/-- The sheafified right whiskered sheafification unit is an isomorphism. -/
theorem isIso_associatedSheaf_map_unit_whiskerRight
    (P B : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :
    IsIso ((𝓛).map ((η).app P ▷ B)) :=
  SheafOfModulesOfCommRing.isIso_associatedSheaf_map_unit_whiskerRight X.sheaf P B

/-- The sheafified left whiskered sheafification unit is an isomorphism. -/
theorem isIso_associatedSheaf_map_whiskerLeft_unit
    (A P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :
    IsIso ((𝓛).map (A ◁ (η).app P)) :=
  SheafOfModulesOfCommRing.isIso_associatedSheaf_map_whiskerLeft_unit X.sheaf A P

/-- The associator of scheme-module tensors: the sheafified presheaf associator conjugated by
the sheafified whiskered sheafification units. -/
def tensorSheafAssociator (M N O : X.Modules) :
    tensorSheaf X (tensorSheaf X M N) O ≅ tensorSheaf X M (tensorSheaf X N O) :=
  SheafOfModulesOfCommRing.tensorAssociator X.sheaf M N O

/-- The original Scheme associator is the actual generic three-factor construction. -/
theorem tensorSheafAssociator_eq_generic (M N O : X.Modules) :
    tensorSheafAssociator X M N O =
      SheafOfModulesOfCommRing.tensorAssociator X.sheaf M N O := rfl

-- The associator is typed on `X.ringCatSheaf`-modules and its factors on the commutative-ring
-- spelling; unfolding it under `simp` needs the transparency override.
set_option backward.isDefEq.respectTransparency false in
/-- The defining square of the associator: precomposed with the sheafified right whiskered
unit, it is the sheafified presheaf associator followed by the sheafified left whiskered
unit. -/
@[reassoc]
theorem map_unit_whiskerRight_comp_tensorSheafAssociator_hom (M N O : X.Modules) :
    (𝓛).map ((η).app ((𝓖).obj M ⊗ (𝓖).obj N) ▷ (𝓖).obj O) ≫
        (tensorSheafAssociator X M N O).hom =
      (𝓛).map (α_ ((𝓖).obj M) ((𝓖).obj N) ((𝓖).obj O)).hom ≫
        (𝓛).map ((𝓖).obj M ◁ (η).app ((𝓖).obj N ⊗ (𝓖).obj O)) :=
  SheafOfModulesOfCommRing.map_unit_whiskerRight_comp_tensorAssociator_hom X.sheaf M N O

-- Rewriting with unit naturality crosses the `X.sheaf` versus `Sheaf J` spellings of the
-- structure sheaf; this needs the transparency override.
set_option backward.isDefEq.respectTransparency false in
/-- The associator on underlying presheaves, through the sheafification units: on the
sectionwise tensor `(M ⊗ N) ⊗ O` it is the presheaf associator followed by the units. -/
theorem associatedSheafUnit_comp_tensorSheafAssociator_hom (M N O : X.Modules) :
    ((η).app ((𝓖).obj M ⊗ (𝓖).obj N) ▷ (𝓖).obj O) ≫
        (η).app ((𝓖).obj ((𝓛).obj ((𝓖).obj M ⊗ (𝓖).obj N)) ⊗ (𝓖).obj O) ≫
          (𝓖).map (tensorSheafAssociator X M N O).hom =
      (α_ ((𝓖).obj M) ((𝓖).obj N) ((𝓖).obj O)).hom ≫
        ((𝓖).obj M ◁ (η).app ((𝓖).obj N ⊗ (𝓖).obj O)) ≫
          (η).app ((𝓖).obj M ⊗ (𝓖).obj ((𝓛).obj ((𝓖).obj N ⊗ (𝓖).obj O))) := by
  exact SheafOfModulesOfCommRing.associatedSheafUnit_comp_tensorAssociator_hom X.sheaf M N O

/-- The associator on nested pure section tensors. -/
theorem tensorSheafAssociator_hom_tmul (M N O : X.Modules) (U : X.Opensᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (o : O.val.obj U) :
    (tensorSheafAssociator X M N O).hom.val.app U
        ((tensorSheafUnit X (tensorSheaf X M N) O).app U
          ((tensorSheafUnit X M N).app U (m ⊗ₜ n) ⊗ₜ o)) =
      (tensorSheafUnit X M (tensorSheaf X N O)).app U
        (m ⊗ₜ (tensorSheafUnit X N O).app U (n ⊗ₜ o)) :=
  SheafOfModulesOfCommRing.tensorAssociator_hom_tmul X.sheaf M N O U m n o

/-- The inverse associator on nested pure section tensors. -/
theorem tensorSheafAssociator_inv_tmul (M N O : X.Modules) (U : X.Opensᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (o : O.val.obj U) :
    (tensorSheafAssociator X M N O).inv.val.app U
        ((tensorSheafUnit X M (tensorSheaf X N O)).app U
          (m ⊗ₜ (tensorSheafUnit X N O).app U (n ⊗ₜ o))) =
      (tensorSheafUnit X (tensorSheaf X M N) O).app U
        ((tensorSheafUnit X M N).app U (m ⊗ₜ n) ⊗ₜ o) :=
  SheafOfModulesOfCommRing.tensorAssociator_inv_tmul X.sheaf M N O U m n o

end AlgebraicGeometry.Scheme.Modules
