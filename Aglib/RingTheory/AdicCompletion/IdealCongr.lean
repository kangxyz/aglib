/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Native completion transport along equality of ideals

Equality transport is performed generically, before specialization to concrete
augmentation kernels. The algebra equivalence preserves the original scalars.
-/

@[expose] public noncomputable section

namespace AdicCompletion

/-- Equal ideals give the same native completion over the original coefficient algebra. -/
def idealCongrAlgEquiv (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I J : Ideal S} (h : I = J) : AdicCompletion I S ≃ₐ[R] AdicCompletion J S := by
  subst J
  exact AlgEquiv.refl

end AdicCompletion
