/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Coalgebra.FiniteDual
public import Aglib.RingTheory.Coalgebra.DualTensor
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Finite-dimensional bialgebra duality

The convolution algebra and transposed multiplication on the native linear dual
form a bialgebra. The same transpose defines morphisms, and native bidual
evaluation gives the bidual equivalence.
-/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct Module.Dual.FiniteDual

namespace Module.Dual

variable (k A : Type*) [Field k] [Ring A] [Bialgebra k A] [FiniteDimensional k A]

theorem dualDistribAlgEquiv_comul (f : Dual k A) :
    TensorProduct.dualDistribAlgEquiv k A A (Coalgebra.comul f) =
      (LinearMap.mul' k A).dualMap f := by
  change (TensorProduct.dualDistribAlgEquiv k A A).toLinearMap (Coalgebra.comul f) = _
  rw [TensorProduct.dualDistribAlgEquiv_toLinearMap]
  apply TensorProduct.ext'
  intro a b
  exact dualDistrib_comul k A f a b

namespace FiniteDual

/-- The bialgebra on the native finite-dimensional linear dual. -/
scoped instance finiteBialgebra : Bialgebra k (Dual k A) :=
  Bialgebra.mk' k (Dual k A)
    (by simp)
    (fun {f g} => by
      simp [convolution_mul_apply, Algebra.TensorProduct.one_def])
    (by
      apply TensorProduct.dual_ext
      intro a b
      simp [Algebra.TensorProduct.one_def])
    (fun {f g} => by
      apply (TensorProduct.dualDistribAlgEquiv k A A).injective
      rw [map_mul (TensorProduct.dualDistribAlgEquiv k A A),
        dualDistribAlgEquiv_comul, dualDistribAlgEquiv_comul,
        dualDistribAlgEquiv_comul]
      exact (Bialgebra.mulCoalgHom k A).dualAlgHom.map_mul f g)

end FiniteDual

end Module.Dual

namespace BialgHom

variable {k A B : Type*} [Field k]
  [Ring A] [Bialgebra k A] [FiniteDimensional k A]
  [Ring B] [Bialgebra k B] [FiniteDimensional k B]

/-- The contravariant transpose of a finite-dimensional bialgebra map. -/
def dual (f : A →ₐc[k] B) : Dual k B →ₐc[k] Dual k A where
  toCoalgHom := f.toAlgHom.dualCoalgHom
  map_one' := f.toCoalgHom.dualAlgHom.map_one
  map_mul' := f.toCoalgHom.dualAlgHom.map_mul

@[simp]
theorem dual_apply (f : A →ₐc[k] B) (g : Dual k B) (a : A) : f.dual g a = g (f a) := rfl

@[simp]
theorem dual_id : (BialgHom.id k A).dual = BialgHom.id k (Dual k A) := by
  ext f a
  rfl

variable {C : Type*} [Ring C] [Bialgebra k C] [FiniteDimensional k C]

@[simp]
theorem dual_comp (f : A →ₐc[k] B) (g : B →ₐc[k] C) :
    (g.comp f).dual = f.dual.comp g.dual := by
  ext h a
  rfl

end BialgHom

namespace Module.Dual

variable (k A : Type*) [Field k] [Ring A] [Bialgebra k A] [FiniteDimensional k A]

/-- Native bidual evaluation, with its original inverse, as an algebra equivalence. -/
def evalAlgEquiv : A ≃ₐ[k] Dual k (Dual k A) :=
  AlgEquiv.ofLinearEquiv (Module.evalEquiv k A)
    (by ext f; rfl)
    (fun a b => by
      apply LinearMap.ext
      intro f
      change f (a * b) = (eval k A a * eval k A b) f
      rw [convolution_mul_apply, TensorProduct.dualDistrib_eval_tmul, dualDistrib_comul])

@[simp]
theorem evalAlgEquiv_apply (a : A) (f : Dual k A) : evalAlgEquiv k A a f = f a := rfl

@[simp]
theorem evalAlgEquiv_toLinearEquiv :
    (evalAlgEquiv k A).toLinearEquiv = Module.evalEquiv k A := rfl

/-- Native bidual evaluation is a bialgebra equivalence on a finite-dimensional bialgebra. -/
def evalBialgEquiv : A ≃ₐc[k] Dual k (Dual k A) where
  __ := Module.evalEquiv k A
  map_mul' := (evalAlgEquiv k A).map_mul
  counit_comp := by ext a; rfl
  map_comp_comul := by
    ext a
    apply TensorProduct.dual_ext
    intro f g
    change TensorProduct.dualDistrib k (Dual k A) (Dual k A)
        (TensorProduct.map (eval k A) (eval k A) (Coalgebra.comul a)) (f ⊗ₜ[k] g) =
      TensorProduct.dualDistrib k (Dual k A) (Dual k A)
        (Coalgebra.comul (eval k A a)) (f ⊗ₜ[k] g)
    rw [TensorProduct.dualDistrib_map_eval, dualDistrib_comul]
    exact (convolution_mul_apply f g a).symm

@[simp]
theorem evalBialgEquiv_apply (a : A) (f : Dual k A) : evalBialgEquiv k A a f = f a := rfl

@[simp]
theorem evalBialgEquiv_toLinearEquiv :
    (evalBialgEquiv k A).toLinearEquiv = Module.evalEquiv k A := rfl

variable {k A} {B : Type*} [Ring B] [Bialgebra k B] [FiniteDimensional k B]

/-- The bidual bialgebra equivalence is natural for the original bialgebra maps. -/
theorem evalBialgEquiv_natural (f : A →ₐc[k] B) :
    f.dual.dual.comp (evalBialgEquiv k A).toBialgHom =
      (evalBialgEquiv k B).toBialgHom.comp f := by
  ext a g
  rfl

variable (k A)

/-- The native bidual equivalence satisfies the triple-dual triangle identity. -/
theorem dual_evalBialgEquiv :
    (evalBialgEquiv k A).toBialgHom.dual =
      (evalBialgEquiv k (Dual k A)).symm.toBialgHom := by
  ext f a
  change f (eval k A a) = (Module.evalEquiv k (Dual k A)).symm f a
  exact (Module.apply_evalEquiv_symm_apply k (Dual k A) (eval k A a) f).symm

end Module.Dual
