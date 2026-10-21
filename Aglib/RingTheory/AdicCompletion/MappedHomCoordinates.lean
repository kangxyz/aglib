/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.ExtendedHomCoordinates
public import Aglib.RingTheory.AdicCompletion.ScalarNaturality

/-! # Completed evaluation coordinates after an original linear parametrization -/

@[expose] public noncomputable section

namespace AdicCompletion

universe u v w
variable {A : Type v} [CommRing A] {B : Type u} [CommRing B] [IsNoetherianRing B]
  [Algebra A B] (I : Ideal A)
variable {H : Type w} [AddCommGroup H] [Module B H] [Module A H] [IsScalarTower A B H]
variable (M : Type u) [AddCommGroup M] [Module B M] [Module A M]
  [IsScalarTower A B M] [Module.Finite B M]
variable (N : Type u) [AddCommGroup N] [Module B N] [Module A N]
  [IsScalarTower A B N] [Module.Finite B N]

/-- Coordinate compatibility is proved before any geometric parametrization is
instantiated. The parameter module need not be finite or complete. -/
theorem extendedHomEvaluation_coordinate_map (ℓ : H →ₗ[B] M →ₗ[B] N)
    (h : AdicCompletion I H) (m : M) (n : ℕ) :
    (completedHomFormalEquiv (I.map (algebraMap A B))
      (map (I.map (algebraMap A B)) ℓ (mapIdealLinearEquiv (S := B) I H h))).val n
        (Submodule.Quotient.mk m) =
      mapIdealQuotientEquiv (S := B) I N n
        (eval I N n (extendedHomEvaluation I M N
          (map I (ℓ.restrictScalars A) h) (of I M m))) := by
  have hz := extendedHomEvaluation_coordinate (B := B) I M N
    (map I (ℓ.restrictScalars A) h) (of I M m) n
  rw [mapIdealLinearEquiv_map] at hz
  simpa only [eval_of, Submodule.mkQ_apply, mapIdealQuotientEquiv_mk] using hz.symm

end AdicCompletion
