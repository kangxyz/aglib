/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor-map injectivity through an equivalence square

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, SHA-256
  `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `docs/WORK_PLAN.md` and
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
namespace LinearMap

/-- Scalar extension preserves a commutative square with equivalent source and target. -/
theorem lTensor_injective_of_equiv_square
    {R K M N M' N' : Type*} [CommRing R] [AddCommGroup K] [Module R K]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N') (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (h : g.comp eM.toLinearMap = eN.toLinearMap.comp f)
    (hf : Function.Injective (f.lTensor K)) : Function.Injective (g.lTensor K) := by
  have hc : (g.lTensor K).comp (eM.lTensor K).toLinearMap =
      (eN.lTensor K).toLinearMap.comp (f.lTensor K) := by
    apply _root_.TensorProduct.ext'
    intro k m
    exact congrArg (fun n ↦ k ⊗ₜ[R] n) (LinearMap.congr_fun h m)
  intro x y hxy
  obtain ⟨x, rfl⟩ := (eM.lTensor K).surjective x
  obtain ⟨y, rfl⟩ := (eM.lTensor K).surjective y
  apply congrArg (eM.lTensor K)
  apply hf
  apply (eN.lTensor K).injective
  exact (LinearMap.congr_fun hc x).symm.trans (hxy.trans (LinearMap.congr_fun hc y))

end LinearMap
end
