/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Canonical algebra scalar extension from an original unit-tensor comparison

A linear scalar-extension isomorphism whose unit tensors are the specified
algebra map proves that the canonical algebra base-change map is bijective.
The resulting algebra equivalence is that canonical map, not a transported
multiplication on an unrelated linear equivalence.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.Algebra

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B] [Algebra R B] [IsScalarTower R S B]

/-- Agreement on the original unit tensors identifies the entire canonical base-change map. -/
theorem baseChangeAlgHom_toLinearMap (f : A →ₐ[R] B) (e : S ⊗[R] A ≃ₗ[S] B)
    (he : ∀ a : A, e (1 ⊗ₜ[R] a) = f a) :
    (AlgHom.liftEquiv R S A B f).toLinearMap = e.toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s a
  rw [AlgHom.toLinearMap_apply, AlgHom.liftEquiv_tmul]
  have h : (s ⊗ₜ[R] a) = s • ((1 : S) ⊗ₜ[R] a) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul]
  exact congrArg (fun b : B => s • b) (he a).symm

/-- The canonical algebra scalar-extension map is an equivalence when the original linear
comparison is an equivalence and preserves every original unit tensor. -/
def baseChangeAlgEquiv (f : A →ₐ[R] B) (e : S ⊗[R] A ≃ₗ[S] B)
    (he : ∀ a : A, e (1 ⊗ₜ[R] a) = f a) : S ⊗[R] A ≃ₐ[S] B :=
  AlgEquiv.ofBijective (AlgHom.liftEquiv R S A B f) (by
    change Function.Bijective (AlgHom.liftEquiv R S A B f).toLinearMap
    rw [baseChangeAlgHom_toLinearMap f e he]
    exact e.bijective)

/-- The resulting equivalence has the prescribed original unit-tensor formula. -/
@[simp] theorem baseChangeAlgEquiv_one_tmul (f : A →ₐ[R] B) (e : S ⊗[R] A ≃ₗ[S] B)
    (he : ∀ a : A, e (1 ⊗ₜ[R] a) = f a) (a : A) :
    baseChangeAlgEquiv f e he (1 ⊗ₜ[R] a) = f a := by
  change AlgHom.liftEquiv R S A B f (1 ⊗ₜ[R] a) = f a
  rw [AlgHom.liftEquiv_tmul, one_smul]

/-- The canonical equivalence retains the complete original linear comparison. -/
theorem baseChangeAlgEquiv_toLinearEquiv (f : A →ₐ[R] B) (e : S ⊗[R] A ≃ₗ[S] B)
    (he : ∀ a : A, e (1 ⊗ₜ[R] a) = f a) :
    (baseChangeAlgEquiv f e he).toLinearEquiv = e := by
  apply LinearEquiv.toLinearMap_injective
  exact baseChangeAlgHom_toLinearMap f e he

end AlgebraicGeometry.Scheme.Modules.Algebra
