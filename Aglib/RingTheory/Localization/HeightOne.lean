/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Ideal.Height

/-!
# Height-one localizations of normal Noetherian domains

The actual prime localization is Dedekind in dimension at most one, and is a
DVR in dimension exactly one. These statements require no regularity assumption.
-/

@[expose] public section

namespace IsLocalization.AtPrime

/-- A localization of a normal Noetherian domain at a prime of height at most
one is a Dedekind domain; the height-zero field case is included. -/
theorem isDedekindDomain_of_height_le_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S p] (hp : p.height ≤ 1) : IsDedekindDomain S := by
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S
    p.primeCompl_le_nonZeroDivisors
  let : IsNoetherianRing S := IsLocalization.isNoetherianRing p.primeCompl S inferInstance
  let : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hd : ringKrullDim S ≤ 1 := by
    rw [ringKrullDim_eq_height p S]
    exact_mod_cast hp
  let : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.mpr hd
  let : Ring.DimensionLEOne S := ⟨fun _ hq ↦ hq.isMaximal_of_ne_bot ‹_›⟩
  exact { (inferInstance : IsDomain S), (inferInstance : IsNoetherianRing S),
    (inferInstance : Ring.DimensionLEOne S), (inferInstance : IsIntegrallyClosed S) with }

/-- A localization of a normal Noetherian domain at a height-one prime is a DVR. -/
theorem isDiscreteValuationRing_of_height_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [IsDomain S] [Algebra R S]
    [IsLocalization.AtPrime S p] (hp : p.height = 1) : IsDiscreteValuationRing S := by
  let : IsDedekindDomain S := isDedekindDomain_of_height_le_one p S hp.le
  let : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  have hp0 : p ≠ ⊥ := by
    intro heq
    simp [heq] at hp
  exact ((IsDiscreteValuationRing.TFAE S (not_isField R hp0 S)).out 1 3).mpr
    (inferInstance : IsDedekindDomain S)

end IsLocalization.AtPrime
