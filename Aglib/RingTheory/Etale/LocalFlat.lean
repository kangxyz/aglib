/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FaithfullyFlatSource
public import Mathlib.RingTheory.Etale.Locus

/-! # Pointwise etaleness from flatness of the original local algebra

Only the specified localization must be flat. The whole source algebra need
not be flat. The Noetherian base guard supplies the existing local formal
smoothness criterion; no polynomial presentation is selected here.
-/

@[expose] public noncomputable section

namespace Algebra

universe u

/-- Over a Noetherian base, an essentially finite-type algebra is etale at
a prime if its original localization is flat and formally unramified. -/
theorem IsEtaleAt.of_flat_localization_of_noetherian
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [EssFiniteType R S]
    (q : Ideal S) [q.IsPrime] [IsUnramifiedAt R q]
    [Module.Flat R (Localization.AtPrime q)] : IsEtaleAt R q := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let : IsLocalHom (algebraMap Rp Sq) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  let : Module.Flat Rp Sq :=
    (Module.flat_iff_of_isLocalization Rp p.primeCompl Sq).mpr inferInstance
  let : EssFiniteType Rp Sq := EssFiniteType.of_comp (R := R) (S := Rp) (T := Sq)
  let : FormallyUnramified Rp Sq := FormallyUnramified.of_restrictScalars R Rp Sq
  let : FormallyEtale Rp Sq := FormallyEtale.of_local_flat_formallyUnramified Rp Sq
  exact FormallyEtale.comp R Rp Sq

end Algebra
