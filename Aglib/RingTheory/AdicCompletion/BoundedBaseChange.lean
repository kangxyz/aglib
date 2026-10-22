/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BoundedTorsion
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Actual completion base change on bounded torsion modules

A finite module killed by a power of the defining ideal is unchanged by the
original scalar-extension map to the completion. This is not faithful flatness
on arbitrary finite modules. The comparison retains every original element
and every original linear map.
-/

@[expose] public noncomputable section
open TensorProduct
namespace AdicCompletion
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
  (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Original extension to completion is invisible on a finite bounded-torsion module. -/
def tensorEquivOfPowKilled (t : ℕ) (hM : I ^ t • (⊤ : Submodule R M) = ⊥) :
    AdicCompletion I R ⊗[R] M ≃ₗ[R] M := by
  letI := IsAdicComplete.of_pow_smul_eq_bot I t hM
  exact ((ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R).trans
    (ofLinearEquiv I M).symm

/-- The comparison preserves the original scalar-extension unit. -/
@[simp]
theorem tensorEquivOfPowKilled_one_tmul (t : ℕ)
    (hM : I ^ t • (⊤ : Submodule R M) = ⊥) (x : M) :
    tensorEquivOfPowKilled I M t hM ((1 : AdicCompletion I R) ⊗ₜ[R] x) = x := by
  let := IsAdicComplete.of_pow_smul_eq_bot I t hM
  change (ofLinearEquiv I M).symm (ofTensorProduct I M (1 ⊗ₜ[R] x)) = x
  rw [ofTensorProduct_tmul, one_smul, ofLinearEquiv_symm_of]

/-- The inverse is literally the original scalar-extension unit. -/
@[simp]
theorem tensorEquivOfPowKilled_symm (t : ℕ)
    (hM : I ^ t • (⊤ : Submodule R M) = ⊥) (x : M) :
    (tensorEquivOfPowKilled I M t hM).symm x = (1 : AdicCompletion I R) ⊗ₜ[R] x := by
  apply (tensorEquivOfPowKilled I M t hM).injective
  rw [LinearEquiv.apply_symm_apply, tensorEquivOfPowKilled_one_tmul]

/-- Invertibility concerns the actual original unit, not an unspecified equivalence. -/
theorem one_tmul_bijective_of_pow_killed (t : ℕ)
    (hM : I ^ t • (⊤ : Submodule R M) = ⊥) :
    Function.Bijective (fun x : M => (1 : AdicCompletion I R) ⊗ₜ[R] x) := by
  have he : (fun x : M => (1 : AdicCompletion I R) ⊗ₜ[R] x) =
      (tensorEquivOfPowKilled I M t hM).symm := by
    funext x
    exact (tensorEquivOfPowKilled_symm I M t hM x).symm
  rw [he]
  exact (tensorEquivOfPowKilled I M t hM).symm.bijective

/-- Original coefficient maps commute with the bounded-torsion identifications. -/
theorem tensorEquivOfPowKilled_naturality
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (t s : ℕ) (hM : I ^ t • (⊤ : Submodule R M) = ⊥)
    (hN : I ^ s • (⊤ : Submodule R N) = ⊥) (φ : M →ₗ[R] N)
    (z : AdicCompletion I R ⊗[R] M) :
    tensorEquivOfPowKilled I N s hN
      (AlgebraTensorModule.map (R := R) (A := AdicCompletion I R) LinearMap.id φ z) =
      φ (tensorEquivOfPowKilled I M t hM z) := by
  obtain ⟨x, rfl⟩ := (one_tmul_bijective_of_pow_killed I M t hM).surjective z
  simp

end AdicCompletion
