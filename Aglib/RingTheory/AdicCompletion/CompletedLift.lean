/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Ext
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # Completed-linear extension of maps from finite modules -/

@[expose] public noncomputable section

namespace AdicCompletion

universe u v
variable {R P : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
  [AddCommGroup P] [Module R P] [Module.Finite R P]
variable {M : Type v} [AddCommGroup M] [Module R M]
  [Module (AdicCompletion I R) M] [IsScalarTower R (AdicCompletion I R) M]

/-- Extend the original map over completed scalars using the canonical finite
module tensor comparison. No tensor-idempotence of the target is assumed. -/
def liftFiniteLinearMap (a : P →ₗ[R] M) : AdicCompletion I P →ₗ[AdicCompletion I R] M :=
  (a.liftBaseChange (AdicCompletion I R)).comp
    (ofTensorProductEquivOfFiniteNoetherian I P).symm.toLinearMap

@[simp]
theorem liftFiniteLinearMap_of (a : P →ₗ[R] M) (x : P) :
    liftFiniteLinearMap I a (of I P x) = a x := by
  simp only [liftFiniteLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ofTensorProductEquivOfFiniteNoetherian_symm_of, LinearMap.liftBaseChange_one_tmul]

/-- For a complete target, the completed-linear tensor extension is exactly
the extension obtained from the original completion maps. -/
theorem liftFiniteLinearMap_restrictScalars [IsAdicComplete I M] (a : P →ₗ[R] M) :
    (liftFiniteLinearMap I a).restrictScalars R =
      (ofLinearEquiv I M).symm.toLinearMap.comp ((map I a).restrictScalars R) := by
  apply linearMap_ext_of I I.fg_of_isNoetherianRing
  intro x
  change liftFiniteLinearMap I a (of I P x) =
    (ofLinearEquiv I M).symm (map I a (of I P x))
  rw [liftFiniteLinearMap_of, map_of, ofLinearEquiv_symm_of]

end AdicCompletion
