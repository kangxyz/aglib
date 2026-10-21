/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Transport of a completion equivalence along an original module equivalence -/

@[expose] public noncomputable section

namespace AdicCompletion

universe u v w z
variable {R : Type u} [CommRing R] (I : Ideal R)
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {P : Type z} [AddCommGroup P] [Module R P]

/-- Transport a completion comparison along the original linear equivalence,
using native completion congruence and the original base-ring action. -/
def equivOfCongr (e : M ≃ₗ[R] N) (g : AdicCompletion I N ≃ₗ[R] P) :
    AdicCompletion I M ≃ₗ[R] P :=
  ((congr I e).restrictScalars R).trans g

/-- The transport sends an original class through the given original equivalence. -/
theorem equivOfCongr_of (e : M ≃ₗ[R] N) (g : AdicCompletion I N ≃ₗ[R] P) (x : M) :
    equivOfCongr I e g (of I M x) = g (of I N (e x)) := by
  change g (congr I e (of I M x)) = _
  rw [congr_apply, map_of]
  rfl

end AdicCompletion
