/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Support.FiniteLength

/-!
# Detecting finite length by support over a Noetherian local ring

A finite module supported at the closed point has finite length. This is the
local-ring specialization of the existing maximal-support criterion.
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module over a Noetherian local ring has finite length when its
support is contained in the closed point. -/
theorem isFiniteLength_of_support_subset_closedPoint
    (hM : support R M ⊆ PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R)) :
    IsFiniteLength R M := by
  apply finiteLength_of_support_maximal R M
  intro p hp
  have heq : p.asIdeal = IsLocalRing.maximalIdeal R :=
    le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) (hM hp)
  rw [heq]
  infer_instance

theorem isFiniteLength_iff_support_subset_closedPoint :
    IsFiniteLength R M ↔
      support R M ⊆ PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R) :=
  ⟨support_subset_closedPoint_of_isFiniteLength,
    isFiniteLength_of_support_subset_closedPoint M⟩

end Module
