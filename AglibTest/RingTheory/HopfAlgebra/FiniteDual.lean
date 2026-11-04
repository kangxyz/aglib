/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.HopfAlgebra.FiniteDual
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! Native consumers of finite Hopf duality, including a finite group algebra in characteristic 2. -/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct Module.Dual.FiniteDual

variable {k A : Type*} [Field k] [Ring A] [HopfAlgebra k A] [FiniteDimensional k A]

example : HopfAlgebra k (Dual k A) := inferInstance

example (f : Dual k A) (a b : A) :
    TensorProduct.dualDistrib k A A (Coalgebra.comul f) (a ⊗ₜ[k] b) = f (a * b) :=
  Module.Dual.dualDistrib_comul k A f a b

example (f : Dual k A) (a : A) :
    HopfAlgebra.antipode k f a = f (HopfAlgebra.antipode k a) :=
  Module.Dual.antipode_apply k A f a

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

example : HopfAlgebra (ZMod 2)
    (Dual (ZMod 2) (AddMonoidAlgebra (ZMod 2) (ZMod 2))) := inferInstance

example : CommRing (Dual (ZMod 2) (AddMonoidAlgebra (ZMod 2) (ZMod 2))) := inferInstance
