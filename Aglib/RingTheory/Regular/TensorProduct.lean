/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.TensorProduct.Map
public import Aglib.RingTheory.Flat.PrincipalQuotient.BaseChange

/-!
# Regular scalars detected by base-changed linear maps

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, SHA-256
  `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open TensorProduct
open LinearMap

section
namespace Algebra

/-- On a unit chart, injectivity after native scalar extension is exactly what
is needed for regularity of the actual scalar equation after that extension. -/
theorem isSMulRegular_of_baseChange_injective_of_linearEquiv
    {R T M : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup M] [Module R M] (f : M →ₗ[R] R) (e : M ≃ₗ[R] R) (a : R)
    (h : ∀ m, f m = e m * a) (hf : Function.Injective (f.baseChange T)) :
    IsSMulRegular T (algebraMap R T a) := by
  have heq : (LinearMap.mulLeft R a).comp e.toLinearMap = f := by
    ext m
    exact (mul_comm _ _).trans (h m).symm
  have hi : Function.Injective ((LinearMap.mulLeft R a).lTensor T) :=
    _root_.LinearMap.lTensor_injective_of_equiv_square e (LinearEquiv.refl R R) f
      (LinearMap.mulLeft R a) (by simpa using heq) hf
  rw [_root_.Algebra.lTensor_mulLeft] at hi
  let E := Algebra.TensorProduct.rid R T T
  have hE : E ((1 : T) ⊗ₜ[R] a) = algebraMap R T a := by simp [E, Algebra.smul_def]
  have hc : IsSMulRegular (T ⊗[R] R) ((1 : T) ⊗ₜ[R] a) ↔
      IsSMulRegular T (algebraMap R T a) :=
    Equiv.isSMulRegular_congr (e := E.toEquiv) fun x ↦ by
      change E (_ * x) = _ * E x
      rw [map_mul, hE]
  exact hc.mp hi

end Algebra
end
