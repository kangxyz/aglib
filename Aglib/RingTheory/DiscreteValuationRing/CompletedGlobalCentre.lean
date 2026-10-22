/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.CompletedPowerSeriesPair
public import Aglib.RingTheory.NeronModification.PrimeCentre

/-! # The actual global centre in the fixed completed power-series DVR pair

The global target remains power series over the actual completion. Localizing
the source at the original polynomial coefficient-prime complement gives an
actual point in the fixed target DVR. Its residue kernel is proved to be the
extension of the original global kernel modulo the uniformizer.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace PowerSeriesLocalization

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type*) (p : R) [Fact (Irreducible p)]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "P" => MvPolynomial ι R
local notation "C" => MvPowerSeries ι Rhat
local notation "qC" => coefficientIdeal Rhat ι (algebraMap R Rhat p)

local instance : Fact (Irreducible (algebraMap R Rhat p)) :=
  ⟨AdicCompletion.irreducible_algebraMap R p (Fact.out : Irreducible p)⟩

/-- The original polynomial-to-completed-series coefficient map. -/
def completedPolynomialInclusion : P →+* C :=
  MvPolynomial.coeToMvPowerSeries.ringHom.comp (MvPolynomial.map (algebraMap R Rhat))

/-- The original polynomial coefficient prime is the inverse image of the actual target prime. -/
theorem comap_completed_coefficientIdeal :
    (qC).comap (completedPolynomialInclusion R ι) =
      ParameterLocalization.parameterIdeal R ι p := by
  ext a
  rw [← ParameterLocalization.ker_map_residue R ι p,
    ← ker_map_residue Rhat ι (algebraMap R Rhat p) (Fact.out : Irreducible _)]
  change MvPowerSeries.map (residue Rhat)
    (MvPolynomial.map (algebraMap R Rhat) a : C) = 0 ↔ MvPolynomial.map (residue R) a = 0
  rw [← (map_eq_zero_iff (completionResidueSeriesEquiv R ι).toRingHom
    (completionResidueSeriesEquiv R ι).injective)]
  change completionResidueSeriesEquiv R ι
    (MvPowerSeries.map (residue Rhat) (MvPolynomial.map (algebraMap R Rhat) a : C)) = 0 ↔
      MvPolynomial.map (residue R) a = 0
  rw [completionResidueSeriesEquiv_polynomial]
  exact MvPolynomial.coe_eq_zero_iff

variable {B : Type*} [CommRing B] [Algebra (MvPolynomial ι R) B]

/-- The localization submonoid uses the ORIGINAL polynomial base and its coefficient prime. -/
def globalSourceDenominators : Submonoid B :=
  (ParameterLocalization.parameterIdeal R ι p).primeCompl.map (algebraMap P B)

/-- Every original source denominator maps outside the fixed target coefficient prime. -/
theorem globalSourceDenominators_le_comap
    (f : B →+* MvPowerSeries ι (AdicCompletion (maximalIdeal R) R))
    (hf : f.comp (algebraMap (MvPolynomial ι R) B) = completedPolynomialInclusion R ι) :
    globalSourceDenominators R ι p (B := B) ≤
      Submonoid.comap f.toMonoidHom (qC).primeCompl := by
  rintro b ⟨a, ha, rfl⟩
  change f (algebraMap P B a) ∉ qC
  rw [show f (algebraMap P B a) = completedPolynomialInclusion R ι a from
    DFunLike.congr_fun hf a]
  change a ∉ (qC).comap (completedPolynomialInclusion R ι)
  rw [comap_completed_coefficientIdeal]
  exact ha

/-- The native localization of the global source at the original base denominators. -/
abbrev GlobalLocalSource := Localization (globalSourceDenominators R ι p (B := B))

/-- The actual localized point, with values in the fixed completed-series DVR. -/
def globalLocalizedPoint (f : B →+* MvPowerSeries ι (AdicCompletion (maximalIdeal R) R))
    (hf : f.comp (algebraMap (MvPolynomial ι R) B) = completedPolynomialInclusion R ι) :
    GlobalLocalSource R ι p (B := B) →+* CompletedRing R ι p :=
  Algebra.NeronModification.localizedPointAtPrime
    (globalSourceDenominators R ι p (B := B)) qC f
    (globalSourceDenominators_le_comap R ι p f hf)

/-- The exact local centre is the extension of the original global quotient kernel.
No independent local centre or target residue point is chosen. -/
theorem ker_residue_globalLocalizedPoint
    (f : B →+* MvPowerSeries ι (AdicCompletion (maximalIdeal R) R))
    (hf : f.comp (algebraMap (MvPolynomial ι R) B) = completedPolynomialInclusion R ι) :
    RingHom.ker ((residue (CompletedRing R ι p)).comp (globalLocalizedPoint R ι p f hf)) =
      (RingHom.ker ((Ideal.Quotient.mk qC).comp f)).map
        (algebraMap B (GlobalLocalSource R ι p (B := B))) := by
  exact Algebra.NeronModification.ker_residue_localizedPointAtPrime_eq_map_quotient_kernel
    (globalSourceDenominators R ι p (B := B)) qC f
    (globalSourceDenominators_le_comap R ι p f hf)

end PowerSeriesLocalization
