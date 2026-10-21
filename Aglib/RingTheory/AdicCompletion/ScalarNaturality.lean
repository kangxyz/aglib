/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.ScalarExtension
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Naturality of the actual extended-ideal completion comparison -/

@[expose] public section

namespace AdicCompletion

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)
variable {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable {N : Type*} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- Extended-ideal quotient comparison preserves original coefficient maps. -/
theorem mapIdealQuotientEquiv_map (f : M →ₗ[B] N) (n : ℕ)
    (x : M ⧸ (I ^ n • ⊤ : Submodule A M)) :
    mapIdealQuotientEquiv (S := B) I N n
        (((f.restrictScalars A).reduceModIdeal (I ^ n)) x) =
      f.reduceModIdeal ((I.map (algebraMap A B)) ^ n)
        (mapIdealQuotientEquiv (S := B) I M n x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [LinearMap.reduceModIdeal_apply, mapIdealQuotientEquiv_mk,
    LinearMap.restrictScalars_apply]

/-- Completion for an extended ideal is natural for original linear maps. -/
theorem mapIdealLinearEquiv_map (f : M →ₗ[B] N) (x : AdicCompletion I M) :
    mapIdealLinearEquiv (S := B) I N (map I (f.restrictScalars A) x) =
      map (I.map (algebraMap A B)) f (mapIdealLinearEquiv (S := B) I M x) := by
  apply AdicCompletion.ext
  intro n
  exact mapIdealQuotientEquiv_map I f n (x.val n)

end AdicCompletion
