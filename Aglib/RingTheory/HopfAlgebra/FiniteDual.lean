/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Bialgebra.FiniteDual
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The Hopf algebra dual to a finite-dimensional Hopf algebra

The native linear dual has the bialgebra constructed in the lower finite-dual
leaf. Its antipode is exactly the transpose of the original antipode. The
`Module.Dual.FiniteDual` scope retains the original scalar actions and selects
convolution multiplication. No characteristic or etaleness restriction is used.
-/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct Module.Dual.FiniteDual

namespace Module.Dual

variable (k A : Type*) [Field k] [Ring A] [HopfAlgebra k A] [FiniteDimensional k A]

namespace FiniteDual

/-- The antipode on the native dual is exactly the transpose of the original antipode. -/
scoped instance finiteHopfAlgebra : HopfAlgebra k (Dual k A) where
  antipode := (HopfAlgebra.antipode k (A := A)).dualMap
  mul_antipode_rTensor_comul := by
    ext f a
    change LinearMap.mul' k (Dual k A)
        (TensorProduct.map (HopfAlgebra.antipode k (A := A)).dualMap LinearMap.id
          (Coalgebra.comul f)) a =
      algebraMap k (Dual k A) (Coalgebra.counit f) a
    rw [mul'_apply]
    rw [← LinearMap.dualMap_id (M₁ := A)]
    rw [TensorProduct.dualDistrib_map_dualMap_apply, dualDistrib_comul_apply]
    change f (LinearMap.mul' k A
        ((HopfAlgebra.antipode k).rTensor A (Coalgebra.comul a))) = _
    rw [HopfAlgebra.mul_antipode_rTensor_comul_apply]
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]
  mul_antipode_lTensor_comul := by
    ext f a
    change LinearMap.mul' k (Dual k A)
        (TensorProduct.map LinearMap.id (HopfAlgebra.antipode k (A := A)).dualMap
          (Coalgebra.comul f)) a =
      algebraMap k (Dual k A) (Coalgebra.counit f) a
    rw [mul'_apply]
    rw [← LinearMap.dualMap_id (M₁ := A)]
    rw [TensorProduct.dualDistrib_map_dualMap_apply, dualDistrib_comul_apply]
    change f (LinearMap.mul' k A
        ((HopfAlgebra.antipode k).lTensor A (Coalgebra.comul a))) = _
    rw [HopfAlgebra.mul_antipode_lTensor_comul_apply]
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]

end FiniteDual

@[simp]
theorem antipode_apply (f : Dual k A) (a : A) :
    HopfAlgebra.antipode k f a = f (HopfAlgebra.antipode k a) := rfl

end Module.Dual
