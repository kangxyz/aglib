/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic

/-! # The two original points of a DVR spectrum

The native generic and closed points are distinct and exhaust the original
spectrum. No replacement two-point space is introduced.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.Spec.DiscreteValuationRing

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The original generic and closed points exhaust the original DVR spectrum. -/
theorem eq_genericPoint_or_closedPoint (x : Spec (.of R)) :
    x = genericPoint (Spec (.of R)) ∨ x = IsLocalRing.closedPoint R := by
  by_cases hx : x.asIdeal = ⊥
  · left
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hx
  · right
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal hx)

/-- A DVR is not a field, so its original closed point is not generic. -/
theorem closedPoint_ne_genericPoint :
    (IsLocalRing.closedPoint R : Spec (.of R)) ≠ genericPoint (Spec (.of R)) := by
  intro h
  rw [genericPoint_eq_bot_of_affine] at h
  have he : IsLocalRing.maximalIdeal R = ⊥ := congrArg PrimeSpectrum.asIdeal h
  exact (Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal R)
    (IsDiscreteValuationRing.not_isField R)) he

end AlgebraicGeometry.Scheme.Spec.DiscreteValuationRing
