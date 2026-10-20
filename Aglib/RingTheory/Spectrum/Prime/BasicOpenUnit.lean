/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The basic open of a unit


Source: `R5Lab.Aglib.RingTheory.Spectrum.Prime.BasicOpenUnit`.
Packet SHA-256:
`664cd5278597c9b86e5768174b6df27cafb1c3b0a66405b063711706affec448`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

universe u

namespace PrimeSpectrum

lemma basicOpen_unit {A : Type u} [CommRing A] (u : A) (hu : IsUnit u) :
    PrimeSpectrum.basicOpen u = ⊤ := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  have h := congrArg PrimeSpectrum.basicOpen hv
  rw [PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_one] at h
  apply top_unique
  rw [← h]
  exact inf_le_left

end PrimeSpectrum
