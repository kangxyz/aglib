/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.FiniteEtale

/-!
# Generic fiber of a base-extended literal normalization

The generic fiber of `D ⊗[A] integralClosure A E` is identified with the same
ambient generic algebra `E`. The comparison is the canonical tensor cancellation
followed by the original normalization generic-fiber equivalence.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace integralClosure

variable (A K E D : Type*) [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [CommRing E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
  [Algebra.IsIntegral K E]
  [CommRing D] [Algebra A D] [Algebra D K] [IsScalarTower A D K]

/-- Tensor cancellation identifies the generic fiber of the actual base-extended
normalization with the original generic algebra. No localization condition on `D` is needed. -/
def localizedGenericFiberEquiv :
    K ⊗[D] (D ⊗[A] integralClosure A E) ≃ₐ[K] E :=
  (Algebra.TensorProduct.cancelBaseChange A D K K (integralClosure A E)).trans
    (genericFiberEquiv A K E)

/-- The generic comparison preserves both structural maps and the original ambient inclusion. -/
@[simp] theorem localizedGenericFiberEquiv_tmul
    (k : K) (d : D) (b : integralClosure A E) :
    localizedGenericFiberEquiv A K E D (k ⊗ₜ[D] (d ⊗ₜ[A] b)) =
      algebraMap K E (algebraMap D K d * k) * (b : E) := by
  simp [localizedGenericFiberEquiv, Algebra.smul_def]

end integralClosure
