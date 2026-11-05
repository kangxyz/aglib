/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.ClosedSupportNormalization

/-! # Nagata, lying over, and rank for the same finite faithful algebra

The actual algebra structure is retained throughout. Finiteness supplies
integrality and Nagata stability; faithfulness supplies lying over. No
normalization square is declared Cartesian.
-/

@[expose] public noncomputable section

universe u

/-- A finite faithful algebra of a Nagata ring stays Nagata, covers every
original prime, and does not increase Krull dimension. -/
theorem IsNagataRing.finite_faithful_rank
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [FaithfulSMul R S] (hR : IsNagataRing.{u, 0} R) :
    IsNagataRing.{u, 0} S ∧
      Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) ∧
      ringKrullDim S ≤ ringKrullDim R :=
  ⟨IsNagataRing.of_finite hR, Algebra.IsIntegral.comap_surjective R S,
    RingHom.IsIntegral.ringKrullDim_le
      (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R S))⟩
