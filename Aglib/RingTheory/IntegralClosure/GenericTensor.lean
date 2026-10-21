/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.FiniteEtale

/-!
# Tensoring a normalization with a generic algebra

For the literal normalization `C` of `A` in `L`, the tensor product `C ⊗[A] E`
with a `K`-algebra is canonically `L ⊗[K] E`. The equivalence preserves the
original `C`-algebra structure and the pure-tensor formula. This is a comparison
of specified algebras, not a flatness or purity theorem.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace integralClosure

variable (A K L E : Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra.IsIntegral K L]
  [CommRing E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]

/-- The generic tensor comparison retains the original normalization as scalar ring. -/
def genericTensorEquiv :
    integralClosure A L ⊗[A] E ≃ₐ[integralClosure A L] L ⊗[K] E := by
  let e : integralClosure A L ⊗[A] E ≃ₐ[A] L ⊗[K] E :=
    (Algebra.TensorProduct.comm A (integralClosure A L) E).trans
      (((Algebra.TensorProduct.cancelBaseChange A K E E (integralClosure A L)).symm.trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E)
          (genericFiberEquiv A K L))).restrictScalars A) |>.trans
      ((Algebra.TensorProduct.comm K E L).restrictScalars A)
  exact { e.toRingEquiv with
    commutes' c := by
      change e (c ⊗ₜ[A] (1 : E)) = (c : L) ⊗ₜ[K] (1 : E)
      simp [e] }

/-- Pure tensors map through the same ambient inclusion. -/
@[simp] theorem genericTensorEquiv_tmul (c : integralClosure A L) (x : E) :
    genericTensorEquiv A K L E (c ⊗ₜ[A] x) = (c : L) ⊗ₜ[K] x := by
  simp [genericTensorEquiv]

end integralClosure
