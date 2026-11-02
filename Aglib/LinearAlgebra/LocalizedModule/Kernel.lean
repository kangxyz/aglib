/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.NonZeroDivisors


/-!
# The original localized kernel is killed by torsion-free targets

Injectivity of the actual native localized map makes its original kernel
torsion. Every original map into a torsion-free target kills this kernel.
No chosen generic coordinates or generic comparison square is introduced.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace LinearMap

variable {R M N M' N' P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  [AddCommGroup P] [Module R P]
  (lM : M →ₗ[R] M') (lN : N →ₗ[R] N')
  [IsLocalizedModule R⁰ lM] [IsLocalizedModule R⁰ lN]
  (f : M →ₗ[R] N)

/-- Injectivity of the actual localized original arrow gives torsion in its
original kernel, with a genuine nonzerodivisor witness. -/
theorem exists_regular_smul_eq_zero_of_localizedMap_injective
    (hf : Function.Injective (IsLocalizedModule.map R⁰ lM lN f))
    {m : M} (hm : f m = 0) : ∃ r : R⁰, (r : R) • m = 0 := by
  have hloc : lM m = 0 := by
    apply hf
    exact (IsLocalizedModule.map_apply R⁰ lM lN f m).trans
      ((congrArg lN hm).trans ((map_zero lN).trans
        (map_zero (IsLocalizedModule.map R⁰ lM lN f)).symm))
  exact (IsLocalizedModule.eq_zero_iff R⁰ lM).mp hloc

/-- Any original torsion-free-target map kills the original kernel once the
native localized forward map is injective. -/
theorem ker_le_of_localizedMap_injective [Module.IsTorsionFree R P]
    (hf : Function.Injective (IsLocalizedModule.map R⁰ lM lN f)) (g : M →ₗ[R] P) :
    LinearMap.ker f ≤ LinearMap.ker g := by
  intro m hm
  obtain ⟨r, hr⟩ := exists_regular_smul_eq_zero_of_localizedMap_injective lM lN f hf hm
  apply ((isRegular_iff_mem_nonZeroDivisors.mpr r.property).smul_eq_zero_iff_right).mp
  exact (g.map_smul (r : R) m).symm.trans ((congrArg g hr).trans (map_zero g))

end LinearMap
