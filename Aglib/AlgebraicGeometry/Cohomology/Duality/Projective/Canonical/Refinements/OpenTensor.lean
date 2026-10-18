/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections

/-!
# Original exterior and tensor arrows on an open square

Both comparisons retain the original sections and the original supplied
sheaf maps. These are the arrows used in the conormal determinant square.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Original exterior restriction followed by the actual section map. -/
def canonicalExteriorOpenMap {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (N : X'.Modules) (n : ℕ) (f : (restrictFunctor j).obj M ⟶ N) :
    (restrictFunctor j).obj (moduleExteriorPower X M n) ⟶ moduleExteriorPower X' N n :=
  (moduleExteriorPowerRestrictionIso j M n).inv ≫
    (moduleExteriorPowerFunctor X' n).map f

/-- The original exterior comparison sends each original wedge to the wedge of the same images. -/
theorem canonicalExteriorOpenMap_wedge {X X' : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] (M : X.Modules) (N : X'.Modules) (n : ℕ)
    (f : M.restrict j ⟶ N) (U : X'.Opens)
    (v : Fin n → (M.restrict j).val.obj (op U)) :
    (canonicalExteriorOpenMap j M N n f).val.app (op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app (op (j ''ᵁ U)) v) =
      (SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf N n).app (op U)
        (fun i => f.val.app (op U) (v i)) :=
  (congrArg (((moduleExteriorPowerFunctor X' n).map f).val.app (op U))
    (moduleExteriorPowerRestrictionIso_inv_mk j M n U v)).trans
      (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk X'.sheaf f n (op U) v)

/-- The original tensor restriction followed by the actual maps of its two factors. -/
def canonicalTensorOpenMap {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    (M N : X.Modules) (M' N' : X'.Modules) (f : M.restrict j ⟶ M')
    (g : N.restrict j ⟶ N') :
    (restrictFunctor j).obj (tensorSheaf X M N) ⟶ tensorSheaf X' M' N' :=
  (tensorRestrictionIso j M N).inv ≫
    (moduleTensorCoefficientMap X' f).app (N.restrict j) ≫
      (moduleTensorLeftFunctor X' M').map g

/-- Both original tensor sections are retained by the original open square comparison. -/
theorem canonicalTensorOpenMap_section {X X' : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] (M N : X.Modules) (M' N' : X'.Modules)
    (f : M.restrict j ⟶ M') (g : N.restrict j ⟶ N') (U : X'.Opens)
    (m : (M.restrict j).val.obj (op U)) (n : (N.restrict j).val.obj (op U)) :
    (canonicalTensorOpenMap j M N M' N' f g).val.app (op U)
      (moduleTensorSection X M N (j ''ᵁ U) m n) =
      moduleTensorSection X' M' N' U (f.val.app (op U) m) (g.val.app (op U) n) := by
  let t := tensorRestrictionIso j M N
  have hi : t.inv.val.app (op U) (moduleTensorSection X M N (j ''ᵁ U) m n) =
      moduleTensorSection X' (M.restrict j) (N.restrict j) U m n :=
    (congrArg (t.inv.val.app (op U)) (tensorRestrictionIso_section j M N U m n).symm).trans
      (congrArg (fun k => k.val.app (op U)
        (moduleTensorSection X' (M.restrict j) (N.restrict j) U m n)) t.hom_inv_id)
  change ((moduleTensorLeftFunctor X' M').map g).val.app (op U)
    (((moduleTensorCoefficientMap X' f).app (N.restrict j)).val.app (op U)
      (t.inv.val.app (op U) _)) = _
  exact (congrArg (fun z => ((moduleTensorLeftFunctor X' M').map g).val.app (op U)
    (((moduleTensorCoefficientMap X' f).app (N.restrict j)).val.app (op U) z)) hi).trans
      ((congrArg (((moduleTensorLeftFunctor X' M').map g).val.app (op U))
        (moduleTensorCoefficientMap_section f (N.restrict j) U m n)).trans
          (moduleTensorLeftFunctor_map_section M' g U (f.val.app (op U) m) n))

end AlgebraicGeometry.Scheme.Modules
