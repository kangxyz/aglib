/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.FractionAway
public import Mathlib.RingTheory.Localization.Pi
public import Mathlib.Algebra.Algebra.Pi

/-!
# Fraction fields of a finite product of DVR branches

One element with nonzero nonunit coordinates simultaneously produces every branch fraction
field. The product localization is proved by the native finite-product localization theorem.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

variable {ι : Type*} [Finite ι] (D : ι → Type*)
  [∀ i, CommRing (D i)] [∀ i, IsDomain (D i)] [∀ i, IsDiscreteValuationRing (D i)]
  (c : ∀ i, D i) (hc : ∀ i, c i ≠ 0) (hcu : ∀ i, ¬ IsUnit (c i))

include hc hcu in
/-- The product of branch fraction fields is obtained by inverting the same element. -/
theorem fractionPi_isLocalizationAway :
    IsLocalization.Away c (∀ i, FractionRing (D i)) := by
  have (i : ι) : IsLocalization ((Submonoid.powers c).map (Pi.evalRingHom D i))
      (FractionRing (D i)) := by
    simpa only [Submonoid.map_powers, Pi.evalRingHom_apply] using
      isLocalizationAway_of_nonzero_nonunit (FractionRing (D i)) (hc i) (hcu i)
  exact (IsLocalization.iff_map_piEvalRingHom D (∀ i, FractionRing (D i))
    (Submonoid.powers c)).mpr inferInstance

/-- A canonical algebra identification, retaining any common base algebra action. -/
def fractionPiAwayAlgEquiv (A : Type*) [CommRing A] [∀ i, Algebra A (D i)] :
    Localization.Away c ≃ₐ[A] ∀ i, FractionRing (D i) := by
  letI := fractionPi_isLocalizationAway D c hc hcu
  exact (IsLocalization.algEquiv (Submonoid.powers c)
    (Localization.Away c) (∀ i, FractionRing (D i))).restrictScalars A

@[simp] theorem fractionPiAwayAlgEquiv_algebraMap
    (A : Type*) [CommRing A] [∀ i, Algebra A (D i)] (x : ∀ i, D i) (i : ι) :
    fractionPiAwayAlgEquiv D c hc hcu A (algebraMap (∀ i, D i) (Localization.Away c) x) i =
      algebraMap (D i) (FractionRing (D i)) (x i) := by
  simp only [fractionPiAwayAlgEquiv, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  rfl

end IsDiscreteValuationRing
