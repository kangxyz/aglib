/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Coalgebra.DualAlgebra

/-! Consumers retaining the native dual carrier and pointwise scalar action. -/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct Module.Dual.FiniteDual

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A] [Coalgebra R A]

example : Ring (Dual R A) := inferInstance
example : Algebra R (Dual R A) := inferInstance
example : SMulCommClass R (Dual R A) (Dual R A) := inferInstance
example : IsScalarTower R (Dual R A) (Dual R A) := inferInstance

example (x : Dual R A ⊗[R] Dual R A) (a : A) :
    LinearMap.mul' R (Dual R A) x a =
      TensorProduct.dualDistrib R A A x (Coalgebra.comul a) :=
  Module.Dual.mul'_apply R A x a
