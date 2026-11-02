/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Dominance of the original map on spectra

The unchanged injective-ring-map argument is relocated from
`Morphisms.SpreadingOut` for finite affine-curve projections.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- An injective ring map induces a dominant morphism on spectra. -/
theorem specMap_dominant_of_injective {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) :
    IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap φ)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot φ).mp hφ]
  exact bot_le

end AlgebraicGeometry.Scheme
