/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Correcting lifts in compatible finite presentations

The kernel transition in a compatible presentation is surjective because its
error lies in an ideal multiple which can be lifted through the upper
surjection. This is not a claim that reduction preserves arbitrary kernels.
The four module universes are independent, and no Noetherianity is needed.
-/

@[expose] public section

namespace LinearMap

universe u v₁ v₂ w₁ w₂

variable {R : Type u} [CommRing R]
variable {P : Type v₁} {P' : Type v₂} {M : Type w₁} {M' : Type w₂}
variable [AddCommGroup P] [AddCommGroup P'] [AddCommGroup M] [AddCommGroup M']
variable [Module R P] [Module R P'] [Module R M] [Module R M']

/-- A compatible square of presentations has surjective kernel transitions
when its upper error is an ideal multiple killed by the free transition. -/
theorem exists_ker_lift_of_smul (J : Ideal R)
    (f : P →ₗ[R] M) (g : P' →ₗ[R] M') (u : P' →ₗ[R] P) (v : M' →ₗ[R] M)
    (hu : Function.Surjective u) (hg : Function.Surjective g)
    (hcomm : v.comp g = f.comp u)
    (hv : v.ker ≤ J • (⊤ : Submodule R M'))
    (hJ : J • (⊤ : Submodule R P') ≤ u.ker)
    (x : P) (hx : f x = 0) :
    ∃ y : P', g y = 0 ∧ u y = x := by
  obtain ⟨z, hz⟩ := hu x
  have hgz : g z ∈ J • (⊤ : Submodule R M') := by
    apply hv
    change v (g z) = 0
    rw [show v (g z) = f (u z) from congrArg (fun k : P' →ₗ[R] M => k z) hcomm,
      hz, hx]
  have hmap : (J • (⊤ : Submodule R P')).map g = J • (⊤ : Submodule R M') := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]
  rw [← hmap] at hgz
  obtain ⟨w, hw, hgw⟩ := hgz
  have huw : u w = 0 := hJ hw
  refine ⟨z - w, ?_, ?_⟩
  · rw [map_sub, hgw, sub_self]
  · rw [map_sub, huw, sub_zero, hz]

end LinearMap
