/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Coalgebra.DualAlgebra
public import Mathlib.LinearAlgebra.Contraction

/-!
# Tensor products of convolution dual algebras

The native tensor-dual map is an algebra homomorphism for convolution. For
finite projective modules, the native tensor-dual equivalence is an algebra
equivalence with exactly the same underlying map.
-/

@[expose] public section

noncomputable section

open Module WithConv
open scoped TensorProduct Module.Dual.FiniteDual

namespace TensorProduct

variable (R A B : Type*) [CommRing R]
  [AddCommGroup A] [Module R A] [Coalgebra R A]
  [AddCommGroup B] [Module R B] [Coalgebra R B]

omit [Coalgebra R A] [Coalgebra R B] in
theorem dualDistrib_tmul_eq (f : Dual R A) (g : Dual R B) :
    dualDistrib R A B (f ⊗ₜ g) = LinearMap.mul' R R ∘ₗ map f g := by
  ext a b
  simp

theorem dualDistrib_mul_tmul (f h : Dual R A) (g j : Dual R B) :
    dualDistrib R A B ((f ⊗ₜ[R] g) * (h ⊗ₜ[R] j)) =
      dualDistrib R A B (f ⊗ₜ[R] g) * dualDistrib R A B (h ⊗ₜ[R] j) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  simp only [dualDistrib_tmul_eq]
  change LinearMap.mul' R R ∘ₗ map (f * h) (g * j) =
    (toConv (LinearMap.mul' R R ∘ₗ map f g) *
      toConv (LinearMap.mul' R R ∘ₗ map h j)).ofConv
  have hm := LinearMap.algHom_comp_convMul_distrib (Algebra.TensorProduct.lmul' R)
    (toConv (map f g)) (toConv (map h j))
  have ht : toConv (map f g) * toConv (map h j) = toConv (map (f * h) (g * j)) :=
    TensorProduct.map_convMul_map (f := toConv f) (g := toConv g)
      (h := toConv h) (k := toConv j)
  simpa only [Algebra.TensorProduct.lmul'_toLinearMap,
    ht, WithConv.ofConv_toConv] using hm

/-- The canonical tensor-dual map is multiplicative for convolution, without finiteness. -/
def dualDistribAlgHom :
    Dual R A ⊗[R] Dual R B →ₐ[R] Dual R (A ⊗[R] B) :=
  AlgHom.ofLinearMap (dualDistrib R A B)
    (by ext a b; simp [Algebra.TensorProduct.one_def, mul_comm])
    (fun x y => by
      induction x using TensorProduct.inductionOn with
      | add x₁ x₂ h₁ h₂ => simp [add_mul, h₁, h₂]
      | tmul f g =>
        induction y using TensorProduct.inductionOn with
        | add y₁ y₂ h₁ h₂ => simp [mul_add, h₁, h₂]
        | tmul h j => exact dualDistrib_mul_tmul R A B f h g j)

@[simp]
theorem dualDistribAlgHom_toLinearMap :
    (dualDistribAlgHom R A B).toLinearMap = dualDistrib R A B := rfl

@[simp]
theorem dualDistribAlgHom_tmul_tmul (f : Dual R A) (g : Dual R B) (a : A) (b : B) :
    dualDistribAlgHom R A B (f ⊗ₜ g) (a ⊗ₜ b) = f a * g b := rfl

variable [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]

/-- The native finite-projective tensor-dual equivalence preserves the convolution algebra. -/
def dualDistribAlgEquiv :
    Dual R A ⊗[R] Dual R B ≃ₐ[R] Dual R (A ⊗[R] B) := by
  refine AlgEquiv.ofLinearEquiv (dualDistribEquiv R A B) ?_ ?_
  · change (dualDistribEquiv R A B).toLinearMap 1 = 1
    rw [toLinearMap_dualDistribEquiv]
    exact (dualDistribAlgHom R A B).map_one
  · intro x y
    change (dualDistribEquiv R A B).toLinearMap (x * y) =
      (dualDistribEquiv R A B).toLinearMap x * (dualDistribEquiv R A B).toLinearMap y
    simp only [toLinearMap_dualDistribEquiv]
    exact (dualDistribAlgHom R A B).map_mul x y

@[simp]
theorem dualDistribAlgEquiv_toLinearMap :
    (dualDistribAlgEquiv R A B).toLinearMap = dualDistrib R A B :=
  toLinearMap_dualDistribEquiv

@[simp]
theorem dualDistribAlgEquiv_toLinearEquiv :
    (dualDistribAlgEquiv R A B).toLinearEquiv = dualDistribEquiv R A B := rfl

end TensorProduct
