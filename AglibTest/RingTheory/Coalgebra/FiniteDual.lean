/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Coalgebra.FiniteDual

/-! Native dual-coalgebra and transposed algebra-map consumers. -/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct

variable {k A B : Type*} [Field k]
  [Ring A] [Algebra k A] [FiniteDimensional k A]
  [Ring B] [Algebra k B] [FiniteDimensional k B]

example : Coalgebra k (Dual k A) := inferInstance

example (f : Dual k A) (a b : A) :
    TensorProduct.dualDistrib k A A (Coalgebra.comul f) (a ⊗ₜ[k] b) = f (a * b) :=
  Module.Dual.dualDistrib_comul k A f a b

example (f : A →ₐ[k] B) (g : Dual k B) (a : A) : f.dualCoalgHom g a = g (f a) :=
  AlgHom.dualCoalgHom_apply f g a
