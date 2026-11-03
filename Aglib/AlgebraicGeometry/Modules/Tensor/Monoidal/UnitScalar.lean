/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.AffineMultiplication
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections


/-!
# Original affine scalar multiplication through the tensor unit

The original unit multiplication, inserted as the first tensor coefficient
and contracted by the original unitor, acts on every original affine module
section by the same scalar. No replacement tensor or section functor is used.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_unit_scalar_section {X : Scheme.{u}} (M : X.Modules)
    (s : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) (m : Γ(M, U)) :
    ((tensorSheafLeftUnit X M).inv ≫ (moduleTensorCoefficientMap X s).app M ≫
      (tensorSheafLeftUnit X M).hom).val.app (op U) m =
    (show Γ(X, U) from s.val.app (op U) (1 : Γ(X, U))) • m := by
  change (tensorSheafLeftUnit X M).hom.val.app (op U)
    (((moduleTensorCoefficientMap X s).app M).val.app (op U)
      ((tensorSheafLeftUnit X M).inv.val.app (op U) m)) = _
  have hi : (tensorSheafLeftUnit X M).inv.val.app (op U) m =
      moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U (1 : Γ(X, U)) m :=
    leftUnitor_inv_moduleTensorSection M U m
  have hc := moduleTensorCoefficientMap_section s M U (1 : Γ(X, U)) m
  exact (congrArg (fun t => (tensorSheafLeftUnit X M).hom.val.app (op U)
    (((moduleTensorCoefficientMap X s).app M).val.app (op U) t)) hi).trans
      ((congrArg (fun t => (tensorSheafLeftUnit X M).hom.val.app (op U) t) hc).trans
        (tensorLeftUnitIso_hom_section X M U _ m))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original affine multiplication through the tensor unit acts by exactly
its original scalar on the native affine section module. -/
theorem affine_tensor_unit_scalar {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (r : R) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((tensorSheafLeftUnit (Spec R) M).inv ≫
      (moduleTensorCoefficientMap (Spec R) (Scheme.Modules.affineMultiplication R r)).app M ≫
      (tensorSheafLeftUnit (Spec R) M).hom) m = r • m := by
  have hr : (Scheme.Modules.affineMultiplication R r).val.app (op ⊤) (1 : Γ(Spec R, ⊤)) =
      (Scheme.ΓSpecIso R).inv r := by
    rw [Scheme.Modules.affineMultiplication_eq_unitMul]
    change 1 * (Spec R).presheaf.map (𝟙 (op (⊤ : (Spec R).Opens)))
      ((Scheme.ΓSpecIso R).inv r) = _
    rw [CategoryTheory.Functor.map_id]
    exact one_mul _
  exact (tensor_unit_scalar_section M (Scheme.Modules.affineMultiplication R r) ⊤ m).trans
    (congrArg (fun a : Γ(Spec R, ⊤) => a • (show Γ(M, ⊤) from m)) hr)

end AlgebraicGeometry.Scheme.Modules
