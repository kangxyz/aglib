/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BoundedPullback
public import Aglib.RingTheory.AdicCompletion.BoundedTorsion
public import Aglib.RingTheory.AdicCompletion.NoetherianRing

/-!
# Finiteness of the native bounded reconstruction

Only the kernel descends from completed scalars to original scalars. The
completed source itself is not claimed finite over the original ring.
Completion comparison is supplied separately.
-/

@[expose] public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
  [Module (AdicCompletion I R) M] [IsScalarTower R (AdicCompletion I R) M]
  [Module.Finite (AdicCompletion I R) M]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- Finiteness of the original fibre product over the native completion.
No cokernel assumption is needed for this part of bounded reconstruction. -/
theorem finite_pullback_of_pow_ker_eq_bot
    (f : M →ₗ[AdicCompletion I R] AdicCompletion I N) (t : ℕ)
    (hker : I ^ t • (f.restrictScalars R).ker = ⊥) :
    Module.Finite R
      (LinearMap.pullbackKernel (f.restrictScalars R) (of I N)) := by
  let : IsNoetherianRing (AdicCompletion I R) := AdicCompletion.isNoetherianRing R I
  have hkill : I ^ t • (⊤ : Submodule R f.ker) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Submodule.smul_le.mpr
    intro a ha x _
    have hz := Submodule.smul_mem_smul ha
      (show x.val ∈ (f.restrictScalars R).ker from x.property)
    rw [hker] at hz
    change a • x = 0
    apply Subtype.ext
    exact hz
  let : Module.Finite R f.ker :=
    finite_of_pow_smul_eq_bot I I.fg_of_isNoetherianRing t hkill
  let : Module.Finite R (f.restrictScalars R).ker :=
    Module.Finite.equiv
      ((Submodule.restrictScalarsEquiv R (AdicCompletion I R) M f.ker).restrictScalars R).symm
  exact LinearMap.finite_pullbackKernel (f.restrictScalars R) (of I N)

end AdicCompletion
