/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.FiniteLength.EulerObstruction

universe u v w x y i j

open TensorProduct

example (R : Type u) [CommRing R] (C : Type v) [AddCommGroup C] [Module R C]
    (P₁ : Type w) [AddCommGroup P₁] [Module R P₁]
    (P₀ : Type x) [AddCommGroup P₀] [Module R P₀]
    (M : Type y) [AddCommGroup M] [Module R M]
    (ι₁ : Type i) [Fintype ι₁] (ι₀ : Type j) [Fintype ι₀]
    (b₁ : Module.Basis ι₁ R P₁) (b₀ : Module.Basis ι₀ R P₀)
    (f : P₁ →ₗ[R] P₀) (g : P₀ →ₗ[R] M)
    (hg : Function.Surjective g) (hex : Function.Exact f g)
    (hC : IsFiniteLength R C) (r : ℕ)
    (hr : Fintype.card ι₀ = Fintype.card ι₁ + r)
    (hlen : Module.length R (C ⊗[R] M) ≤ r * Module.length R C) :
    Function.Injective (f.lTensor C) :=
  TensorProduct.injective_lTensor_of_length_le b₁ b₀ f g hg hex hC r hr hlen

example (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type x) [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hg : Function.Surjective g) (hex : Function.Exact f g) :
    Module.length R P + Module.length R M =
      Module.length R N + Module.length R (LinearMap.ker f) :=
  LinearMap.length_euler_of_exact f g hg hex
