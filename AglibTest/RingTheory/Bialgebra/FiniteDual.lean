/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Bialgebra.FiniteDual

/-! Native morphism and bidual-evaluation consumers of finite bialgebra duality. -/

@[expose] public section

noncomputable section

open Module
open scoped Module.Dual.FiniteDual

variable {k A B : Type*} [Field k]
  [Ring A] [Bialgebra k A] [FiniteDimensional k A]
  [Ring B] [Bialgebra k B] [FiniteDimensional k B]

example : A ≃ₐc[k] Dual k (Dual k A) := Module.Dual.evalBialgEquiv k A

example : (Module.Dual.evalBialgEquiv k A).toLinearEquiv = Module.evalEquiv k A :=
  Module.Dual.evalBialgEquiv_toLinearEquiv k A

example (f : A →ₐc[k] B) :
    f.dual.dual.comp (Module.Dual.evalBialgEquiv k A).toBialgHom =
      (Module.Dual.evalBialgEquiv k B).toBialgHom.comp f :=
  Module.Dual.evalBialgEquiv_natural f

example : (Module.Dual.evalBialgEquiv k A).toBialgHom.dual =
    (Module.Dual.evalBialgEquiv k (Dual k A)).symm.toBialgHom :=
  Module.Dual.dual_evalBialgEquiv k A
