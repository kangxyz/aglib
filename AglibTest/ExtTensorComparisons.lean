/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.Algebra.Category.ModuleCat.Tensor.ExtOne
import Aglib.Algebra.Category.ModuleCat.Tensor.ExtOneCoefficient
import Aglib.LinearAlgebra.TensorProduct.DualInjectivity

/-! Actual independent-universe Ext consumers of both tensor comparisons. -/

noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

universe u w

example (R : Type u) [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Flat R S.X₁] [Projective S.X₂] [Module.Finite R S.X₃] :
    ∃ e : Ext.{w} S.X₃ (ModuleCat.of R (Module.Dual R (Module.Dual R S.X₃))) 1 →ₗ[R]
        Ext.{w} (ModuleCat.of R (S.X₃ ⊗[R] Module.Dual R S.X₃)) (ModuleCat.of R R) 1,
      Function.Injective e := by
  have hf := LinearMap.rTensor_dual_injective_of_flat S.X₃ S.f.hom
    hS.moduleCat_injective_f
  exact ⟨ModuleCat.extOneDualTensorLinearMap (Module.Dual R S.X₃) hS hf,
    ModuleCat.extOneDualTensorLinearMap_injective (Module.Dual R S.X₃) hS hf⟩

example (R : Type u) [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂]
    (N : ModuleCat.{u} R) :
    (Ext.{w} S.X₃ (ModuleCat.of R R) 1 ⊗[R] N) ≃ₗ[R] Ext.{w} S.X₃ N 1 :=
  ModuleCat.extOneTensorCoefficientLinearEquiv N hS
