/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # A principal localization acting on the specified original fraction field

All data are the original ring, denominator and chosen fraction field. The
canonical localization map supplies the algebra action, its tower and fraction
property together. No auxiliary embedding is hidden in a typeclass instance.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace Localization.AwayChosenFraction

variable (R K : Type*) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (d : R) [NeZero d]

/-- The principal multiplicative set consists of actual nonzero elements. -/
theorem powers_le_nonZeroDivisors : Submonoid.powers d ≤ nonZeroDivisors R :=
  Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne d))

/-- The canonical map retains the specified fraction field and denominator. -/
abbrev map : Localization.Away d →ₐ[R] K :=
  Localization.mapToFractionRing K (Submonoid.powers d) (Localization.Away d)
    (powers_le_nonZeroDivisors R d)

/-- The actual localization action; the chosen field is not replaced. -/
@[instance_reducible] def algebra : Algebra (Localization.Away d) K :=
  (map R K d).toRingHom.toAlgebra

/-- The chosen fraction field as an algebra over the principal localization. -/
local instance awayAlgebraOfChosenFraction : Algebra (Localization.Away d) K := algebra R K d

/-- The action has the original ring map as its composite. -/
theorem algebraMap_comp :
    (algebraMap (Localization.Away d) K).comp (algebraMap R (Localization.Away d)) =
      algebraMap R K :=
  (map R K d).comp_algebraMap

/-- The actual localization action has the original scalar tower. -/
theorem tower : IsScalarTower R (Localization.Away d) K :=
  IsScalarTower.of_algebraMap_eq' (algebraMap_comp R K d).symm

local instance : IsScalarTower R (Localization.Away d) K := tower R K d

/-- The same specified field is the fraction field of the principal localization. -/
theorem fractionRing : IsFractionRing (Localization.Away d) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers d) (Localization.Away d) K

/-- Nonzero localization retains an integral domain. -/
theorem domain : IsDomain (Localization.Away d) :=
  Localization.Away.isDomain (NeZero.ne d)

end Localization.AwayChosenFraction
