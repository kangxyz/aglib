/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IsSepClosed

/-! # Infinitude of separably closed fields -/

@[expose] public section

/-- A separably closed field is infinite: a finite field would be perfect,
and hence algebraically closed, contradicting its finiteness. -/
theorem IsSepClosed.infinite (K : Type*) [Field K] [IsSepClosed K] : Infinite K := by
  by_contra h
  let : Finite K := not_infinite_iff_finite.mp h
  let : IsAlgClosed K := inferInstance
  exact (inferInstance : Infinite K).not_finite inferInstance
