/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Coefficient maps on fraction fields of multivariate power series

Injectivity is proved coefficientwise, then native fraction-ring lifting
constructs the actual map and its formula on series.
-/

@[expose] public noncomputable section

namespace MvPowerSeries

/-- Coefficientwise application of an injective hom is injective. -/
lemma coefficientMap_injective {R S σ : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (MvPowerSeries.map (σ := σ) f) := by
  intro x y h
  apply MvPowerSeries.ext
  intro d
  apply hf
  simpa only [coeff_map] using congrArg (coeff d) h

/-- The actual induced map of fraction fields of series rings. -/
def fractionCoefficientMap {R S σ : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Injective f) :
    FractionRing (MvPowerSeries σ R) →+* FractionRing (MvPowerSeries σ S) :=
  IsFractionRing.lift (K := FractionRing (MvPowerSeries σ R))
    (g := (algebraMap (MvPowerSeries σ S) (FractionRing (MvPowerSeries σ S))).comp
      (MvPowerSeries.map f))
    ((IsFractionRing.injective (MvPowerSeries σ S) (FractionRing (MvPowerSeries σ S))).comp
      (coefficientMap_injective f hf))

@[simp]
lemma fractionCoefficientMap_algebraMap {R S σ : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Injective f)
    (x : MvPowerSeries σ R) :
    fractionCoefficientMap f hf (algebraMap _ (FractionRing (MvPowerSeries σ R)) x) =
      algebraMap _ (FractionRing (MvPowerSeries σ S)) (MvPowerSeries.map f x) := by
  unfold fractionCoefficientMap
  exact IsFractionRing.lift_algebraMap _ x

/-- In particular, the embedding into series over the fraction coefficient field
is literal coefficientwise localization followed by fraction-ring lifting. -/
abbrev fractionToCoefficientFraction (R σ : Type*) [CommRing R] [IsDomain R] :
    FractionRing (MvPowerSeries σ R) →+* FractionRing (MvPowerSeries σ (FractionRing R)) :=
  fractionCoefficientMap (algebraMap R (FractionRing R))
    (IsFractionRing.injective R (FractionRing R))

end MvPowerSeries
