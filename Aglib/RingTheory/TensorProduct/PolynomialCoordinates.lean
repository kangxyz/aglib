/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Coordinates of the canonical polynomial-tensor equivalence

The source maps and equivalence reuse `(polyEquivTensor' R A).symm` and
its inverse; no second polynomial scalar-extension object is defined.

Source: `R5Lab.Aglib.RingTheory.TensorProduct.PolynomialCoordinates`.
Packet SHA-256:
`ec9bbb3cc523599a753321db697f2bf27b38b06292cb1d75f025613577ed9c38`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
open scoped TensorProduct Polynomial

namespace Polynomial

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The canonical inverse polynomial-tensor equivalence on pure tensors. -/
theorem polyEquivTensor'_symm_tmul (a : A) (p : R[X]) :
    (polyEquivTensor' R A).symm (a ⊗ₜ[R] p) = C a * p.map (algebraMap R A) := by
  simpa only [coe_polyEquivTensor'_symm, smul_eq_C_mul] using
    polyEquivTensor_symm_apply_tmul_eq_smul R A a p

/-- The canonical polynomial-tensor equivalence sends constants to coefficient tensors. -/
@[simp] theorem polyEquivTensor'_C (a : A) :
    polyEquivTensor' R A (C a) = a ⊗ₜ[R] (1 : R[X]) := by
  simp [polyEquivTensor_apply]

/-- The canonical polynomial-tensor equivalence sends the variable to its literal tensor. -/
@[simp] theorem polyEquivTensor'_X :
    polyEquivTensor' R A (X : A[X]) = 1 ⊗ₜ[R] (X : R[X]) := by
  simp [polyEquivTensor_apply]

/-- The forward scalar-extension map retains the literal coefficient ring map. -/
@[simp] theorem polyEquivTensor'_symm_includeRight (p : R[X]) :
    (polyEquivTensor' R A).symm (1 ⊗ₜ[R] p) = p.map (algebraMap R A) := by
  simp

end Polynomial
