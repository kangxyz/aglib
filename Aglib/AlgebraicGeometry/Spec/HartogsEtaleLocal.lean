/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsFiniteFlatLocal
public import Mathlib.RingTheory.Unramified.LocalRing

/-! # Original punctured scalars under an essentially etale local map

Equality of the extended maximal ideal with the target maximal ideal identifies
exactly the original closed-point fibre and hence the original punctured opens.
Flat scalar base change transports the original scalar bijection. No normality
or domain hypothesis is imposed on either ring in these transport statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable {A B : Type u} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B]

/-- Equality of the extended maximal ideals identifies the entire original
closed-point fibre, without an integrality assumption. -/
theorem specMap_eq_closedPoint_iff_of_map_maximalIdeal
    (σ : A →+* B)
    (hσ : (IsLocalRing.maximalIdeal A).map σ = IsLocalRing.maximalIdeal B)
    (q : Spec (.of B)) :
    Spec.map (CommRingCat.ofHom σ) q = IsLocalRing.closedPoint A ↔
      q = IsLocalRing.closedPoint B := by
  let : IsLocalHom σ :=
    ((IsLocalRing.local_hom_TFAE σ).out 3 1 rfl rfl).mp hσ.le
  constructor
  · intro hq
    have hc : q.asIdeal.comap σ = IsLocalRing.maximalIdeal A :=
      congrArg PrimeSpectrum.asIdeal hq
    have hm : IsLocalRing.maximalIdeal B ≤ q.asIdeal := by
      rw [← hσ, Ideal.map_le_iff_le_comap, hc]
    apply PrimeSpectrum.ext
    exact le_antisymm (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) hm
  · rintro rfl
    apply PrimeSpectrum.ext
    exact IsLocalRing.maximalIdeal_comap σ

/-- The literal inverse image of the punctured spectrum is the target
punctured spectrum. No replacement of the affine spectra is made. -/
theorem preimage_puncturedSpecOpen_of_map_maximalIdeal
    (σ : A →+* B)
    (hσ : (IsLocalRing.maximalIdeal A).map σ = IsLocalRing.maximalIdeal B) :
    Spec.map (CommRingCat.ofHom σ) ⁻¹ᵁ puncturedSpecOpen A = puncturedSpecOpen B := by
  ext q
  change (Spec.map (CommRingCat.ofHom σ) q ≠ IsLocalRing.closedPoint A) ↔
    q ≠ IsLocalRing.closedPoint B
  exact not_congr (specMap_eq_closedPoint_iff_of_map_maximalIdeal σ hσ q)

/-- Flat base change along the original scalar square transports an actual
punctured scalar bijection; neither coefficient ring is assumed normal. -/
theorem puncturedAffineScalar_bijective_of_flat_of_map_maximalIdeal
    [QuasiCompact (puncturedSpecOpen A).ι]
    (σ : A →+* B) (hflat : σ.Flat)
    (hσ : (IsLocalRing.maximalIdeal A).map σ = IsLocalRing.maximalIdeal B)
    (hA : Function.Bijective (affineScalarMap (puncturedSpecOpen A).ι)) :
    Function.Bijective (affineScalarMap (puncturedSpecOpen B).ι) := by
  let U := puncturedSpecOpen A
  let l := Spec.map (CommRingCat.ofHom σ)
  have h := Cohomology.scalarSections_bijective_of_flat_of_isPullback
    (l ∣_ U) σ (l ⁻¹ᵁ U).ι U.ι (isPullback_morphismRestrict l U) hflat hA
  have hp : l ⁻¹ᵁ U = puncturedSpecOpen B :=
    preimage_puncturedSpecOpen_of_map_maximalIdeal σ hσ
  change Function.Bijective (affineScalarMap (l ⁻¹ᵁ U).ι) at h
  rw [hp] at h
  exact h

variable [Algebra A B] [IsLocalHom (algebraMap A B)]
  [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]

/-- The original essentially finite type unramified local map has precisely
one point in its closed fibre. -/
theorem specMap_eq_closedPoint_iff_of_formallyUnramified (q : Spec (.of B)) :
    Spec.algebraMap A B q = IsLocalRing.closedPoint A ↔
      q = IsLocalRing.closedPoint B :=
  specMap_eq_closedPoint_iff_of_map_maximalIdeal (algebraMap A B)
    Algebra.FormallyUnramified.map_maximalIdeal q

/-- The unramified local map preserves the literal punctured open. -/
theorem preimage_puncturedSpecOpen_of_formallyUnramified :
    Spec.algebraMap A B ⁻¹ᵁ puncturedSpecOpen A = puncturedSpecOpen B :=
  preimage_puncturedSpecOpen_of_map_maximalIdeal (algebraMap A B)
    Algebra.FormallyUnramified.map_maximalIdeal

/-- In particular, an essentially etale local scalar change preserves an
existing Hartogs scalar bijection on the original punctured spectrum. -/
theorem puncturedAffineScalar_bijective_of_flat_formallyUnramified
    [QuasiCompact (puncturedSpecOpen A).ι]
    [Module.Flat A B]
    (hA : Function.Bijective (affineScalarMap (puncturedSpecOpen A).ι)) :
    Function.Bijective (affineScalarMap (puncturedSpecOpen B).ι) :=
  puncturedAffineScalar_bijective_of_flat_of_map_maximalIdeal (algebraMap A B)
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
    Algebra.FormallyUnramified.map_maximalIdeal hA

end AlgebraicGeometry.Scheme
