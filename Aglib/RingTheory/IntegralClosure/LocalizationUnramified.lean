/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.Localization
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Unramified.Basic

/-! # Formal unramifiedness at a prime of the original normalization

Localization of the base identifies the literal integral closures by their
original ambient inclusion. Further localization at a specified prime uses
the native localization lift, without replacing the normalization or assuming
that its prime localization is integral over the base.
-/

@[expose] public noncomputable section

namespace Algebra.FormallyUnramified

variable (R S S' : Type*) [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']

/-- A further prime localization retains formal unramifiedness of the original
base map. The intermediate map is the native localization lift. -/
theorem atPrime_of_localization (M : Submonoid S) [IsLocalization M S']
    [FormallyUnramified R S'] (q : Ideal S) [q.IsPrime] (hM : M ≤ q.primeCompl) :
    FormallyUnramified R (Localization.AtPrime q) := by
  let Q := Localization.AtPrime q
  let : Algebra S' Q :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S' Q M q.primeCompl hM
  let : IsScalarTower S S' Q :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S' Q M q.primeCompl hM
  let : IsScalarTower R S' Q := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R S S',
      ← IsScalarTower.algebraMap_apply S S' Q,
      ← IsScalarTower.algebraMap_apply R S Q]
  let : IsLocalization (q.primeCompl.map (algebraMap S S')) Q :=
    IsLocalization.isLocalization_of_submonoid_le S' Q M q.primeCompl hM
  let : FormallyUnramified S' Q :=
    FormallyUnramified.of_isLocalization (q.primeCompl.map (algebraMap S S'))
  exact FormallyUnramified.comp R S' Q

/-- Formal unramifiedness on the original principal open holds at each prime
not containing its defining element. -/
theorem atPrime_of_away (x : S) [FormallyUnramified R (Localization.Away x)]
    (q : Ideal S) [q.IsPrime] (hx : x ∉ q) :
    FormallyUnramified R (Localization.AtPrime q) :=
  atPrime_of_localization R S (Localization.Away x) (Submonoid.powers x) q
    (Submonoid.powers_le.mpr hx)

end Algebra.FormallyUnramified

namespace integralClosure

variable (R D A : Type*) [CommRing R] [CommRing D] [CommRing A]
  [Algebra R D] [Algebra D A] [Algebra R A] [IsScalarTower R D A]

/-- Formal unramifiedness of the literal normalization after localization of
the base implies formal unramifiedness at the specified prime of the original
normalization. The normalization and ambient generic algebra may be disconnected.
In particular, a proved etaleness theorem for the localized normalization supplies
the formal-unramifiedness hypothesis. -/
theorem formallyUnramified_atPrime_of_localized
    (q : Ideal (integralClosure R A)) [q.IsPrime]
    [IsLocalization.AtPrime D (q.under R)]
    [Algebra.FormallyUnramified D (integralClosure D A)] :
    Algebra.FormallyUnramified R (Localization.AtPrime q) := by
  let : Algebra (integralClosure R A) (integralClosure D A) :=
    scalarExtensionAlgebra R D A
  let : IsScalarTower R (integralClosure R A) (integralClosure D A) :=
    scalarExtension_isScalarTower_base R D A
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure R A) (q.under R).primeCompl)
      (integralClosure D A) :=
    scalarExtension_isLocalization R D A (q.under R).primeCompl
  let : Algebra.FormallyUnramified R D :=
    Algebra.FormallyUnramified.of_isLocalization (q.under R).primeCompl
  let : Algebra.FormallyUnramified R (integralClosure D A) :=
    Algebra.FormallyUnramified.comp R D (integralClosure D A)
  apply Algebra.FormallyUnramified.atPrime_of_localization R (integralClosure R A)
    (integralClosure D A)
    (Algebra.algebraMapSubmonoid (integralClosure R A) (q.under R).primeCompl) q
  rintro _ ⟨r, hr, rfl⟩
  exact hr

end integralClosure
