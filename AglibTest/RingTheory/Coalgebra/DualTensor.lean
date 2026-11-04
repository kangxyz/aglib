/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Coalgebra.DualTensor

/-! The algebra tensor-dual equivalence retains the original native linear equivalence. -/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct Module.Dual.FiniteDual

variable {R A B : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [Coalgebra R A]
  [AddCommGroup B] [Module R B] [Coalgebra R B]

example (f : Dual R A) (g : Dual R B) (a : A) (b : B) :
    TensorProduct.dualDistribAlgHom R A B (f ⊗ₜ[R] g) (a ⊗ₜ[R] b) = f a * g b :=
  TensorProduct.dualDistribAlgHom_tmul_tmul R A B f g a b

example [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B] :
    (TensorProduct.dualDistribAlgEquiv R A B).toLinearEquiv =
      TensorProduct.dualDistribEquiv R A B :=
  TensorProduct.dualDistribAlgEquiv_toLinearEquiv R A B
