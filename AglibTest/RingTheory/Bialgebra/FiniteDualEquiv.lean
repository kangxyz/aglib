/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Bialgebra.FiniteDualEquiv

/-! The bialgebra dual equivalence retains the native linear equivalence and its inverse. -/

@[expose] public section

open scoped Module.Dual.FiniteDual

variable {k A B : Type*} [Field k]
  [Ring A] [Bialgebra k A] [FiniteDimensional k A]
  [Ring B] [Bialgebra k B] [FiniteDimensional k B] (e : A ≃ₐc[k] B)

example : e.dual.toLinearEquiv = e.toLinearEquiv.dualMap := rfl

example : e.dual.symm.toLinearEquiv = e.symm.toLinearEquiv.dualMap := by
  rw [BialgEquiv.dual_symm, BialgEquiv.dual_toLinearEquiv]

example (f : Module.Dual k A →ₐc[k] B) :
    (Module.Dual.evalBialgEquiv k B).symm.toBialgHom.comp
        ((Module.Dual.evalBialgEquiv k A).symm.toBialgHom.comp f.dual).dual = f :=
  BialgHom.dual_eval_symm_comp f
