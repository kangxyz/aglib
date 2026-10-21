/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompletedHom
public import Aglib.RingTheory.AdicCompletion.ScalarExtension

/-! # Completed Hom evaluation after restricting the base ring -/

@[expose] public noncomputable section

namespace AdicCompletion

universe u v
variable {A : Type v} [CommRing A] {B : Type u} [CommRing B] [IsNoetherianRing B]
  [Algebra A B] (I : Ideal A)
variable (M : Type u) [AddCommGroup M] [Module B M] [Module A M]
  [IsScalarTower A B M] [Module.Finite B M]
variable (N : Type u) [AddCommGroup N] [Module B N] [Module A N]
  [IsScalarTower A B N] [Module.Finite B N]

/-- Evaluate completed linear maps using completion for the original base ideal.
Finiteness is required only over the larger ring, not over the structural base. -/
def extendedHomEvaluation :
    AdicCompletion I (M →ₗ[B] N) →ₗ[A]
      AdicCompletion I M →ₗ[A] AdicCompletion I N := by
  let J := I.map (algebraMap A B)
  let eH := mapIdealLinearEquiv (S := B) I (M →ₗ[B] N)
  let eM := mapIdealLinearEquiv (S := B) I M
  let eN := mapIdealLinearEquiv (S := B) I N
  let e := completedHomEquiv J M N
  refine {
    toFun := fun h => {
      toFun := fun m => eN.symm (e (eH h) (eM m))
      map_add' := ?_
      map_smul' := ?_ }
    map_add' := ?_
    map_smul' := ?_ }
  · intro x y
    simp only [map_add]
  · intro a x
    change eN.symm (e (eH h) (eM (a • x))) = a • eN.symm (e (eH h) (eM x))
    rw [eM.map_smul]
    exact (congrArg eN.symm
      (((e (eH h)).restrictScalars B).map_smul_of_tower a (eM x))).trans
        (eN.symm.map_smul a _)
  · intro h k
    apply LinearMap.ext
    intro x
    simp only [map_add, LinearMap.add_apply]
    rfl
  · intro a h
    apply LinearMap.ext
    intro x
    change eN.symm (e (eH (a • h)) (eM x)) = a • eN.symm (e (eH h) (eM x))
    have he : e (a • eH h) (eM x) = a • e (eH h) (eM x) := by
      simpa only [IsScalarTower.algebraMap_smul, LinearMap.smul_apply,
        LinearEquiv.restrictScalars_apply] using
        congrArg (fun z => z (eM x))
          ((e.restrictScalars B).map_smul (algebraMap A B a) (eH h))
    exact (congrArg (fun z => eN.symm (e z (eM x))) (eH.map_smul a h)).trans
      ((congrArg eN.symm he).trans (eN.symm.map_smul a _))

/-- Completed evaluation agrees with the original bilinear evaluation on classes. -/
@[simp]
theorem extendedHomEvaluation_of_of (f : M →ₗ[B] N) (m : M) :
    extendedHomEvaluation I M N (of I (M →ₗ[B] N) f) (of I M m) = of I N (f m) := by
  have h : (mapIdealLinearEquiv (S := B) I N).symm
      (of (I.map (algebraMap A B)) N (f m)) = of I N (f m) :=
    (LinearEquiv.symm_apply_eq _).mpr (mapIdealLinearEquiv_of (S := B) I N (f m)).symm
  simpa [extendedHomEvaluation, mapIdealLinearEquiv_of, map_of] using h

end AdicCompletion
