/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.HartogsSections
public import Aglib.RingTheory.KrullDimension.GoingDown

/-! # Hartogs sections on the original going-down pullback

Going down keeps the inverse image of a codimension-two complement away from
height-one points. Normality is required only of the original source ring.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.HasGoingDown A B]

/-- The original contraction of a height-one point has height at most one. -/
theorem height_one_mem_goingDownPullback (U : (Spec (.of A)).Opens)
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 → p ∈ U)
    (q : PrimeSpectrum B) (hq : q.asIdeal.height = 1) :
    q ∈ Spec.algebraMap A B ⁻¹ᵁ U := by
  apply hU (PrimeSpectrum.comap (algebraMap A B) q)
  exact (Ideal.height_under_le_of_hasGoingDown (R := A) q.asIdeal).trans_eq hq

/-- The actual scalar restriction on a nonempty going-down pullback is bijective. -/
theorem hartogsGoingDownPullbackScalar_bijective
    [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (U : (Spec (.of A)).Opens) [Nonempty (Spec.algebraMap A B ⁻¹ᵁ U)]
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 → p ∈ U) :
    Function.Bijective (hartogsScalarMap B (Spec.algebraMap A B ⁻¹ᵁ U)) :=
  hartogsScalarMap_bijective B _ (height_one_mem_goingDownPullback A B U hU)

/-- The complement of the closed point has codimension at least two after
any going-down map from the original local base. -/
theorem height_one_mem_puncturedGoingDownPullback [IsLocalRing A]
    (hdim : 2 ≤ ringKrullDim A) (q : PrimeSpectrum B)
    (hq : q.asIdeal.height = 1) :
    q ∈ Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A := by
  apply height_one_mem_goingDownPullback A B _ _ q hq
  intro p hp he
  have heq : p = IsLocalRing.closedPoint A := he
  have hmax : (IsLocalRing.maximalIdeal A).height ≤ 1 := by
    rw [heq] at hp
    exact hp
  have hd := hdim
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at hd
  have : (2 : WithBot ℕ∞) ≤ 1 := hd.trans (WithBot.coe_le_coe.mpr hmax)
  norm_num at this

end AlgebraicGeometry.Scheme
