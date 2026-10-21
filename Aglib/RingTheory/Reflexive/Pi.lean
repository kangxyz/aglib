/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Finite products preserve the native double-dual reflexivity predicate. -/

@[expose] public section

namespace Module

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]

/-- A finite dependent product of reflexive modules is reflexive. -/
instance IsReflexive.pi :
    ∀ {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, IsReflexive R (M i)], IsReflexive R (∀ i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h ↦ Module.equiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih ↦ Module.equiv (LinearEquiv.piOptionEquivProd R).symm

/-- The nondependent finite-product instance, useful when inference does not recognize a
constant dependent family. -/
instance IsReflexive.pi' {M : Type*} [AddCommGroup M] [Module R M] [IsReflexive R M] :
    IsReflexive R (ι → M) := IsReflexive.pi

end Module
