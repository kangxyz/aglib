/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.ExtendedHom
public import Aglib.RingTheory.AdicCompletion.FormalHom

/-! # Original quotient coordinates of structural completed evaluation -/

@[expose] public noncomputable section

namespace AdicCompletion

universe u v
variable {A : Type v} [CommRing A] {B : Type u} [CommRing B] [IsNoetherianRing B]
  [Algebra A B] (I : Ideal A)
variable (M : Type u) [AddCommGroup M] [Module B M] [Module A M]
  [IsScalarTower A B M] [Module.Finite B M]
variable (N : Type u) [AddCommGroup N] [Module B N] [Module A N]
  [IsScalarTower A B N] [Module.Finite B N]

/-- Completed Hom elements are determined by their structural evaluation maps. -/
theorem extendedHomEvaluation_injective :
    Function.Injective (extendedHomEvaluation (B := B) I M N) := by
  intro h k hk
  apply (mapIdealLinearEquiv (S := B) I (M →ₗ[B] N)).injective
  apply (completedHomEquiv (I.map (algebraMap A B)) M N).injective
  apply LinearMap.ext
  intro m
  obtain ⟨m, rfl⟩ := (mapIdealLinearEquiv (S := B) I M).surjective m
  apply (mapIdealLinearEquiv (S := B) I N).symm.injective
  exact LinearMap.congr_fun hk m

/-- The structural completed pairing has exactly the coordinates supplied by
the finite completed-Hom equivalence over the extended ideal. -/
theorem extendedHomEvaluation_coordinate
    (h : AdicCompletion I (M →ₗ[B] N)) (m : AdicCompletion I M) (n : ℕ) :
    mapIdealQuotientEquiv (S := B) I N n
        (eval I N n (extendedHomEvaluation I M N h m)) =
      (completedHomFormalEquiv (I.map (algebraMap A B))
        (mapIdealLinearEquiv (S := B) I (M →ₗ[B] N) h)).val n
          (mapIdealQuotientEquiv (S := B) I M n (eval I M n m)) := by
  let J := I.map (algebraMap A B)
  let eH := mapIdealLinearEquiv (S := B) I (M →ₗ[B] N)
  let eM := mapIdealLinearEquiv (S := B) I M
  let eN := mapIdealLinearEquiv (S := B) I N
  let e := completedHomEquiv J M N
  change eval J N n (eN (eN.symm (e (eH h) (eM m)))) =
    formalHomComponent J (IsNoetherian.noetherian J) (e (eH h)) n (eval J M n (eM m))
  rw [eN.apply_symm_apply]
  exact (formalHomComponent_eval J (IsNoetherian.noetherian J) (e (eH h)) n (eM m)).symm

end AdicCompletion
