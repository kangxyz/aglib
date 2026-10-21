/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.Dual
public import Mathlib.RingTheory.TensorProduct.Finite

/-! Hom modules with finite reflexive target over a Noetherian domain are reflexive. -/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Module

/-- Hom into a finite reflexive module is reflexive, by the actual evaluation equivalence
and tensor-Hom currying. -/
theorem IsReflexive.linearMap {R M N : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [IsReflexive R N] : IsReflexive R (M →ₗ[R] N) := by
  let e : (M →ₗ[R] N) ≃ₗ[R] Dual R (M ⊗[R] Dual R N) :=
    (LinearEquiv.congrRight (evalEquiv R N)).trans
      (TensorProduct.lift.equiv (RingHom.id R) M (Dual R N) R)
  let := IsReflexive.dual_of_finite (R := R) (M := M ⊗[R] Dual R N)
  exact Module.equiv e.symm

end Module
