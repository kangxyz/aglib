/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Bialgebra.FiniteDual

/-!
# Native transpose of finite-dimensional bialgebra equivalences

The underlying equivalence and inverse are exactly `LinearEquiv.dualMap`.
The bialgebra laws are those of the previously constructed transpose map.
-/

@[expose] public section

noncomputable section

open Module
open scoped Module.Dual.FiniteDual

namespace BialgEquiv

variable {k A B C : Type*} [Field k]
  [Ring A] [Bialgebra k A] [FiniteDimensional k A]
  [Ring B] [Bialgebra k B] [FiniteDimensional k B]
  [Ring C] [Bialgebra k C] [FiniteDimensional k C]

/-- The original native dual linear equivalence, with the proved bialgebra-map laws. -/
def dual (e : A ≃ₐc[k] B) : Dual k B ≃ₐc[k] Dual k A where
  __ := e.toLinearEquiv.dualMap
  map_mul' := e.toBialgHom.dual.map_mul
  counit_comp := e.toBialgHom.dual.counit_comp
  map_comp_comul := e.toBialgHom.dual.map_comp_comul

@[simp]
theorem dual_apply (e : A ≃ₐc[k] B) (f : Dual k B) (a : A) : e.dual f a = f (e a) := rfl

theorem dual_toLinearEquiv (e : A ≃ₐc[k] B) :
    e.dual.toLinearEquiv = e.toLinearEquiv.dualMap := rfl

theorem dual_toBialgHom (e : A ≃ₐc[k] B) : e.dual.toBialgHom = e.toBialgHom.dual := by
  ext f a
  rfl

@[simp]
theorem dual_refl : (BialgEquiv.refl k A).dual = BialgEquiv.refl k (Dual k A) := by
  ext f a
  rfl

@[simp]
theorem dual_symm (e : A ≃ₐc[k] B) : e.dual.symm = e.symm.dual := by
  ext f a
  rfl

/-- The same original transpose reverses composition of equivalences. -/
theorem dual_trans (e : A ≃ₐc[k] B) (f : B ≃ₐc[k] C) :
    (e.trans f).dual = f.dual.trans e.dual := by
  ext g a
  rfl

end BialgEquiv

namespace BialgHom

variable {k A B : Type*} [Field k]
  [Ring A] [Bialgebra k A] [FiniteDimensional k A]
  [Ring B] [Bialgebra k B] [FiniteDimensional k B]

/-- Transposing the whole inverse-evaluation composite recovers the original bialgebra map. -/
theorem dual_eval_symm_comp (f : Dual k A →ₐc[k] B) :
    (Module.Dual.evalBialgEquiv k B).symm.toBialgHom.comp
        ((Module.Dual.evalBialgEquiv k A).symm.toBialgHom.comp f.dual).dual = f := by
  ext x
  apply (Module.Dual.evalBialgEquiv k B).injective
  change (Module.Dual.evalBialgEquiv k B)
      ((Module.Dual.evalBialgEquiv k B).symm
        (((Module.Dual.evalBialgEquiv k A).symm.toBialgHom.comp f.dual).dual x)) =
      (Module.Dual.evalBialgEquiv k B) (f x)
  rw [BialgEquiv.apply_symm_apply]
  ext y
  exact Module.apply_evalEquiv_symm_apply k A x (f.dual y)

end BialgHom
