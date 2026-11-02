/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.SplitAdicSections
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Original Hartogs scalars after finite flat local base change

An integral map of local rings has precisely the closed point over the
closed point. Thus the actual inverse image of the punctured spectrum is
the punctured spectrum. Flat scalar base change then transports the original
normal-base Hartogs theorem to a possibly nonnormal, nonintegral local ring.
No depth-only effectivity or finite-etale essential surjectivity is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable {A B : Type u} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B]

/-- Integrality and locality identify the entire closed-point fibre. No
domain, normality, or flatness assumption is needed for this equality. -/
theorem specMap_eq_closedPoint_iff_of_integral
    (σ : A →+* B) (hσ : σ.IsIntegral) (q : Spec (.of B)) :
    Spec.map (CommRingCat.ofHom σ) q = IsLocalRing.closedPoint A ↔
      q = IsLocalRing.closedPoint B := by
  constructor
  · intro hq
    let : q.asIdeal.IsPrime := q.isPrime
    have hc : (q.asIdeal.comap σ).IsMaximal := by
      have he : q.asIdeal.comap σ = IsLocalRing.maximalIdeal A :=
        congrArg PrimeSpectrum.asIdeal hq
      rw [he]
      infer_instance
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap σ hσ q.asIdeal hc)
  · rintro rfl
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal σ hσ
        (IsLocalRing.maximalIdeal B))

/-- The original punctured opens, with no replacement of either spectrum. -/
theorem preimage_puncturedSpecOpen_of_integral
    (σ : A →+* B) (hσ : σ.IsIntegral) :
    Spec.map (CommRingCat.ofHom σ) ⁻¹ᵁ puncturedSpecOpen A = puncturedSpecOpen B := by
  ext q
  change (Spec.map (CommRingCat.ofHom σ) q ≠ IsLocalRing.closedPoint A) ↔
    q ≠ IsLocalRing.closedPoint B
  exact not_congr (specMap_eq_closedPoint_iff_of_integral σ hσ q)

/-- The native affine scalar map on the new punctured local spectrum is
bijective. The new ring B need not be a domain or normal. -/
theorem puncturedAffineScalar_bijective_of_finite_flat
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (σ : A →+* B) (hfinite : σ.Finite) (hflat : σ.Flat)
    (hdim : 2 ≤ ringKrullDim A) :
    Function.Bijective (affineScalarMap (puncturedSpecOpen B).ι) := by
  let U := puncturedSpecOpen A
  let l := Spec.map (CommRingCat.ofHom σ)
  have hU : Function.Bijective (affineScalarMap U.ι) := by
    have h := puncturedSpecScalarMap_bijective A hdim
    rw [← affineScalarMap_topIso (puncturedSpecOpen A)] at h
    exact Function.Bijective.of_comp_left
      (f := (puncturedSpecOpen A).topIso.hom.hom)
      (g := affineScalarMap (puncturedSpecOpen A).ι) h
      (ConcreteCategory.bijective_of_isIso (puncturedSpecOpen A).topIso.hom).injective
  have h := Cohomology.scalarSections_bijective_of_flat_of_isPullback
    (l ∣_ U) σ (l ⁻¹ᵁ U).ι U.ι (isPullback_morphismRestrict l U) hflat hU
  have hp : l ⁻¹ᵁ U = puncturedSpecOpen B :=
    preimage_puncturedSpecOpen_of_integral σ hfinite.to_isIntegral
  change Function.Bijective (affineScalarMap (l ⁻¹ᵁ U).ι) at h
  rw [hp] at h
  exact h

/-- In ambient open-section coordinates the map is exactly the original
constant restriction of B, not an independently selected scalar isomorphism. -/
theorem puncturedSpecScalarMap_bijective_of_finite_flat
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (σ : A →+* B) (hfinite : σ.Finite) (hflat : σ.Flat)
    (hdim : 2 ≤ ringKrullDim A) :
    Function.Bijective (hartogsScalarMap B (puncturedSpecOpen B)) := by
  rw [← affineScalarMap_topIso (puncturedSpecOpen B)]
  exact (ConcreteCategory.bijective_of_isIso (puncturedSpecOpen B).topIso.hom).comp
    (puncturedAffineScalar_bijective_of_finite_flat σ hfinite hflat hdim)

end AlgebraicGeometry.Scheme
