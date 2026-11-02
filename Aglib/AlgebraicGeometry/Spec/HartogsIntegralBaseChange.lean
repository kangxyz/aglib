/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.HartogsIntegralPullback
public import Aglib.AlgebraicGeometry.Spec.SplitAdicSections

/-! # Flat base change of original normal integral Hartogs sections

The canonical scalar map on the actual pulled-back open is bijective. Its
input is the original normal integral cover and the height-one condition on
the base open; no post-base-change normality or scalar equivalence is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable (A B : Type u) [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [IsIntegrallyClosed A] [IsIntegrallyClosed B]
  [IsNoetherianRing B] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
  (U : (Spec (.of A)).Opens) [Nonempty U]
  (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → p ∈ U)

include hU
omit [IsDomain A] in
/-- The unchanged normal-source scalar map is bijective in native top coordinates. -/
theorem hartogsIntegralPullbackAffineScalar_bijective :
    Function.Bijective (affineScalarMap (Spec.algebraMap A B ⁻¹ᵁ U).ι) := by
  let V := Spec.algebraMap A B ⁻¹ᵁ U
  have h := hartogsIntegralPullbackScalar_bijective A B U hU
  rw [← affineScalarMap_topIso V] at h
  exact Function.Bijective.of_comp_left
    (f := V.topIso.hom.hom) (g := affineScalarMap V.ι) h
    (ConcreteCategory.bijective_of_isIso V.topIso.hom).injective

include hU
omit [IsDomain A] in
/-- Arbitrary flat base change retains the original normal cover's Hartogs
section identification, without normality of the new source. -/
theorem hartogsIntegralPullbackAffineScalar_bijective_of_flat
    {T : Type u} [CommRing T] (σ : B →+* T) (hσ : σ.Flat)
    {Y : Scheme.{u}} (p : Y ⟶ (Spec.algebraMap A B ⁻¹ᵁ U).toScheme)
    (q : Y ⟶ Spec (.of T))
    (H : IsPullback p q (Spec.algebraMap A B ⁻¹ᵁ U).ι
      (Spec.map (CommRingCat.ofHom σ))) : Function.Bijective (affineScalarMap q) := by
  exact Cohomology.scalarSections_bijective_of_flat_of_isPullback
    p σ q (Spec.algebraMap A B ⁻¹ᵁ U).ι H hσ
    (hartogsIntegralPullbackAffineScalar_bijective A B U hU)

end AlgebraicGeometry.Scheme
