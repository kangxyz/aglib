/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.HartogsSections
public import Aglib.RingTheory.KrullDimension.IntegralExtension

/-! # Original Hartogs sections after an integral normal pullback

Going down over the normal base preserves prime heights. Thus the inverse
image of an open containing the height-one points still contains every
height-one point of the original normal integral source. This identifies
its actual section ring with the original source ring; no finite model or
reflexive replacement is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable (A B : Type u) [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [IsIntegrallyClosed A] [IsIntegrallyClosed B]
  [IsNoetherianRing B] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
  (U : (Spec (.of A)).Opens) [Nonempty U]

omit [IsDomain A] [IsDomain B] [IsIntegrallyClosed A]
  [IsIntegrallyClosed B] [IsNoetherianRing B] in
/-- Lying over makes the original inverse-image open nonempty. -/
theorem integralPullbackOpen_nonempty : Nonempty (Spec.algebraMap A B ⁻¹ᵁ U) := by
  obtain ⟨x⟩ := ‹Nonempty U›
  obtain ⟨y, hy⟩ := Algebra.IsIntegral.comap_surjective A B x.val
  refine ⟨⟨y, ?_⟩⟩
  change PrimeSpectrum.comap (algebraMap A B) y ∈ U
  rw [hy]
  exact x.property

omit [IsDomain A] in
/-- The original normal source has unchanged sections over the pulled-back
Hartogs open. Integrality, rather than finite degree, is enough. -/
theorem hartogsIntegralPullbackScalar_bijective
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → p ∈ U) :
    Function.Bijective (hartogsScalarMap B (Spec.algebraMap A B ⁻¹ᵁ U)) := by
  let := integralPullbackOpen_nonempty A B U
  apply hartogsScalarMap_bijective B (Spec.algebraMap A B ⁻¹ᵁ U)
  intro q hq
  apply hU (PrimeSpectrum.comap (algebraMap A B) q)
  exact (Ideal.height_eq_height_under_of_normal (R := A) q.asIdeal).symm.trans hq

/-- The full equivalence retains the original scalar restriction as forward map. -/
def hartogsIntegralPullbackSectionsEquiv
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → p ∈ U) :
    B ≃+* Γ(Spec (.of B), Spec.algebraMap A B ⁻¹ᵁ U) :=
  RingEquiv.ofBijective _ (hartogsIntegralPullbackScalar_bijective A B U hU)

end AlgebraicGeometry.Scheme
