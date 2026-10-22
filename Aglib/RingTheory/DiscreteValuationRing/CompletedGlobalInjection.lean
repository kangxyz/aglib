/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.CompletedGlobalCentre

/-! # Injectivity of the actual localized global point -/

@[expose] public noncomputable section

open IsLocalRing

namespace PowerSeriesLocalization

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type*) (p : R) [Fact (Irreducible p)]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "P" => MvPolynomial ι R
local notation "C" => MvPowerSeries ι Rhat
local notation "qC" => coefficientIdeal Rhat ι (algebraMap R Rhat p)

local instance : IsDomain C := NoZeroDivisors.to_isDomain _
local instance : Fact (Irreducible (algebraMap R Rhat p)) :=
  ⟨AdicCompletion.irreducible_algebraMap R p (Fact.out : Irreducible p)⟩

variable {B : Type*} [CommRing B] [Algebra (MvPolynomial ι R) B]

/-- The actual point of the localized source is injective whenever the global point is. -/
theorem globalLocalizedPoint_injective
    (f : B →+* MvPowerSeries ι (AdicCompletion (maximalIdeal R) R))
    (hf : f.comp (algebraMap (MvPolynomial ι R) B) = completedPolynomialInclusion R ι)
    (hfinj : Function.Injective f) :
    Function.Injective (globalLocalizedPoint R ι p f hf) := by
  apply IsLocalization.map_injective_of_injective'
    (M := globalSourceDenominators R ι p (B := B))
    (S := C) (CompletedRing R ι p)
    (globalSourceDenominators_le_comap R ι p f hf)
    (show (0 : C) ∉ (qC).primeCompl from fun h => h (qC).zero_mem) hfinj

/-- Domain of the localized original source follows from the actual target injection. -/
theorem globalLocalSource_isDomain
    (f : B →+* MvPowerSeries ι (AdicCompletion (maximalIdeal R) R))
    (hf : f.comp (algebraMap (MvPolynomial ι R) B) = completedPolynomialInclusion R ι)
    (hfinj : Function.Injective f) :
    IsDomain (GlobalLocalSource R ι p (B := B)) :=
  Function.Injective.isDomain (globalLocalizedPoint R ι p f hf)
    (globalLocalizedPoint_injective R ι p f hf hfinj)

end PowerSeriesLocalization
