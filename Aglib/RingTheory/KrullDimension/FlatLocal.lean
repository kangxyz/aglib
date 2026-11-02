/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.KrullDimension.GoingDown
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.RingHom.Flat

/-! # Dimension under the original flat local map

Going down at the actual maximal ideal bounds the original local dimensions.
No Noetherianity or finite-presentation assumption is needed.
-/

@[expose] public section

namespace RingHom

/-- A flat local ring map cannot decrease local Krull dimension. -/
theorem ringKrullDim_le_of_flat_local
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : f.Flat) : ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := (RingHom.flat_algebraMap_iff).mp hf
  have h := Ideal.height_under_le_of_hasGoingDown (R := R) (IsLocalRing.maximalIdeal S)
  change ((IsLocalRing.maximalIdeal S).comap f).height ≤ _ at h
  rw [IsLocalRing.maximalIdeal_comap f] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_le_coe.mpr h

end RingHom
