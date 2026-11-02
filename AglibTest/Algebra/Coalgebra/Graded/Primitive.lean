/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Coalgebra.Graded.Primitive
public import Mathlib.Data.ZMod.Basic

/-! A native characteristic-two consumer: two distinct primitive
degree-one basis elements have nonzero product, without factorial division. -/

open scoped TensorProduct

@[expose] public noncomputable section

variable {A : Type*} [Ring A] [Algebra (ZMod 2) A] [Nontrivial A]
  (𝒜 : ℕ → Submodule (ZMod 2) A) [GradedAlgebra 𝒜] [Coalgebra (ZMod 2) A]

example
    (hε : ∀ a, GradedAlgebra.proj 𝒜 0 a = Coalgebra.counit (R := ZMod 2) a • (1 : A))
    (h_one : Coalgebra.comul (R := ZMod 2) (1 : A) = (1 : A) ⊗ₜ[ZMod 2] (1 : A))
    (h_mul : ∀ a b : A,
      GradedTensorProduct.of (ZMod 2) 𝒜 𝒜 (Coalgebra.comul (a * b)) =
        GradedTensorProduct.of (ZMod 2) 𝒜 𝒜 (Coalgebra.comul a) *
          GradedTensorProduct.of (ZMod 2) 𝒜 𝒜 (Coalgebra.comul b))
    (b : Module.Basis (Fin 2) (ZMod 2) (𝒜 1))
    (hb : ∀ i, Coalgebra.IsSkewPrimitiveElem (ZMod 2) (1 : A) 1 (b i : A)) :
    (b 0 : A) * (b 1 : A) ≠ 0 := by
  simpa using GradedAlgebra.basis_list_prod_ne_zero 𝒜 hε h_one h_mul b hb
    [(0 : Fin 2), 1] (by decide)
