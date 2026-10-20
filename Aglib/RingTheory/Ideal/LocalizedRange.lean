/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Localization of the range ideal of a linear functional

Extracted from `R5Lab.Aglib.AlgebraicGeometry.Divisors.Relative.ZeroLocus`
at R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
The localization and the two linear functionals are the original actual maps.
The result has no scheme or Noetherian hypothesis.
-/

@[expose] public section

namespace Ideal

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
variable [IsScalarTower R S N]
variable (W : Submonoid R) [IsLocalization W S]
variable (l : M →ₗ[R] N) [IsLocalizedModule W l]
variable (a : M →ₗ[R] R) (b : N →ₗ[S] S)

include W in
/-- A localized linear functional has the extension of the original range ideal. -/
theorem map_range_of_isLocalizedModule (h : ∀ m, b (l m) = algebraMap R S (a m)) :
    Ideal.map (algebraMap R S) (LinearMap.range a : Ideal R) = LinearMap.range b := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    rintro x ⟨m, rfl⟩
    exact ⟨l m, h m⟩
  · rintro y ⟨n, rfl⟩
    obtain ⟨⟨m, w⟩, hw⟩ := IsLocalizedModule.surj W l n
    have hm : algebraMap R S (a m) ∈ Ideal.map (algebraMap R S) (LinearMap.range a : Ideal R) :=
      Ideal.mem_map_of_mem (algebraMap R S) ⟨m, rfl⟩
    have he : algebraMap R S w * b n = algebraMap R S (a m) := by
      calc
        algebraMap R S w * b n = b ((w : R) • n) := by
          rw [← Algebra.smul_def, b.map_smul_of_tower]
        _ = b (l m) := congrArg b hw
        _ = _ := h m
    rw [← he] at hm
    exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S w)).mp hm

end Ideal
