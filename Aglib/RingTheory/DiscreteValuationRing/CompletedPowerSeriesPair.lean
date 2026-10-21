/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.DiscreteValuationRing
public import Aglib.RingTheory.DiscreteValuationRing.ParameterMap
public import Aglib.RingTheory.DiscreteValuationRing.PowerSeriesParameterMap

/-!
# The original polynomial and completed power-series DVR pair

The source is the original coefficient-uniformizer localization of the polynomial
ring. The target is the coefficient-uniformizer localization of power series over
the actual maximal-ideal completion. The literal residue map becomes the canonical
rational-function to power-series fraction map under the proved residue comparisons.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace PowerSeriesLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v)

local notation "Rhat" => AdicCompletion (maximalIdeal R) R

local instance : IsDomain (MvPowerSeries ι (ResidueField R)) :=
  NoZeroDivisors.to_isDomain _

local instance : IsDomain (MvPowerSeries ι Rhat) :=
  NoZeroDivisors.to_isDomain _

local instance : IsDomain (MvPowerSeries ι (ResidueField Rhat)) :=
  NoZeroDivisors.to_isDomain _

/-- The coefficientwise series equivalence induced by the actual completion residue map. -/
def completionResidueSeriesEquiv :
    MvPowerSeries ι (ResidueField Rhat) ≃+* MvPowerSeries ι (ResidueField R) where
  __ := MvPowerSeries.map (AdicCompletion.residueFieldEquiv R).toRingHom
  invFun := MvPowerSeries.map (AdicCompletion.residueFieldEquiv R).symm.toRingHom
  left_inv f := by
    ext d
    exact (AdicCompletion.residueFieldEquiv R).symm_apply_apply (f.coeff d)
  right_inv f := by
    ext d
    exact (AdicCompletion.residueFieldEquiv R).apply_symm_apply (f.coeff d)

/-- The same comparison on the actual fraction fields. -/
def completionResidueFractionEquiv :
    FractionRing (MvPowerSeries ι (ResidueField Rhat)) ≃+*
      FractionRing (MvPowerSeries ι (ResidueField R)) :=
  IsFractionRing.ringEquivOfRingEquiv (completionResidueSeriesEquiv R ι)

/-- The original coefficient completion and residue comparison commute literally. -/
theorem completionResidueEquiv_residue (r : R) :
    AdicCompletion.residueFieldEquiv R (residue Rhat (algebraMap R Rhat r)) = residue R r := by
  rw [← ResidueField.map_residue]
  exact AdicCompletion.residueFieldEquiv_map R _

/-- Original polynomial inclusion followed by completion, reduction and comparison. -/
theorem completionResidueSeriesEquiv_polynomial (f : MvPolynomial ι R) :
    completionResidueSeriesEquiv R ι
      (MvPowerSeries.map (residue Rhat)
        (MvPolynomial.map (algebraMap R Rhat) f : MvPowerSeries ι Rhat)) =
      (MvPolynomial.map (residue R) f : MvPowerSeries ι (ResidueField R)) := by
  let lhs : MvPolynomial ι R →+* MvPowerSeries ι (ResidueField R) :=
    (completionResidueSeriesEquiv R ι).toRingHom.comp
      ((MvPowerSeries.map (residue Rhat)).comp
        (MvPolynomial.coeToMvPowerSeries.ringHom.comp
          (MvPolynomial.map (algebraMap R Rhat))))
  let rhs : MvPolynomial ι R →+* MvPowerSeries ι (ResidueField R) :=
    MvPolynomial.coeToMvPowerSeries.ringHom.comp (MvPolynomial.map (residue R))
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change MvPowerSeries.map (AdicCompletion.residueFieldEquiv R).toRingHom
        (MvPowerSeries.map (residue Rhat)
          (↑(MvPolynomial.map (algebraMap R Rhat)
            (MvPolynomial.C r : MvPolynomial ι R)) : MvPowerSeries ι Rhat)) = _
      simp only [MvPolynomial.map_C, MvPolynomial.coe_C, MvPowerSeries.map_C]
      change MvPowerSeries.C
        (AdicCompletion.residueFieldEquiv R (residue Rhat (algebraMap R Rhat r))) =
          rhs (MvPolynomial.C r)
      rw [completionResidueEquiv_residue R r]
      simp only [rhs, RingHom.comp_apply, MvPolynomial.map_C,
        MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C]
    · intro i
      simp [lhs, rhs, completionResidueSeriesEquiv]
  exact DFunLike.congr_fun h f

variable (p : R) [Fact (Irreducible p)]

local instance : Fact (Irreducible (algebraMap R Rhat p)) :=
  ⟨AdicCompletion.irreducible_algebraMap R p (Fact.out : Irreducible p)⟩

/-- The actual target localization, with the image of the original uniformizer. -/
abbrev CompletedRing := Ring Rhat ι (algebraMap R Rhat p)

/-- The target is a DVR, not merely a ring assumed to be isomorphic to one. -/
theorem completedRing_isDiscreteValuationRing [Finite ι] :
    IsDiscreteValuationRing (CompletedRing R ι p) :=
  isDiscreteValuationRing Rhat ι (algebraMap R Rhat p)

/-- Its residue field expressed over the original residue field. -/
def completedResidueFieldEquiv :
    ResidueField (CompletedRing R ι p) ≃+*
      FractionRing (MvPowerSeries ι (ResidueField R)) :=
  (residueFieldRingEquiv Rhat ι (algebraMap R Rhat p)).trans
    (completionResidueFractionEquiv R ι)

variable [Finite ι]

/-- The original polynomial localization maps to the actual completed-series localization. -/
def completedPolynomialMap : ParameterLocalization.Ring R ι p →+* CompletedRing R ι p :=
  (polynomialMap Rhat ι (algebraMap R Rhat p)).comp
    (ParameterLocalization.parameterMap R Rhat ι p).toRingHom

instance completedPolynomialMap_isLocalHom : IsLocalHom (completedPolynomialMap R ι p) := by
  let : IsLocalHom (ParameterLocalization.parameterMap R Rhat ι p).toRingHom :=
    ParameterLocalization.parameterMap_isLocalHom R Rhat ι p
  exact RingHom.isLocalHom_comp _ _

@[simp] theorem completedPolynomialMap_polynomial (f : MvPolynomial ι R) :
    completedPolynomialMap R ι p
        (algebraMap (MvPolynomial ι R) (ParameterLocalization.Ring R ι p) f) =
      algebraMap (MvPowerSeries ι Rhat) (CompletedRing R ι p)
        (MvPolynomial.map (algebraMap R Rhat) f : MvPowerSeries ι Rhat) := by
  change polynomialMap Rhat ι (algebraMap R Rhat p)
    (ParameterLocalization.parameterMap R Rhat ι p
      (algebraMap (MvPolynomial ι R) (ParameterLocalization.Ring R ι p) f)) = _
  rw [ParameterLocalization.parameterMap_polynomial, polynomialMap_polynomial]

/-- The actual composite remains injective. -/
theorem completedPolynomialMap_injective : Function.Injective (completedPolynomialMap R ι p) :=
  (polynomialMap_injective Rhat ι (algebraMap R Rhat p)).comp
    (ParameterLocalization.parameterMap_injective R Rhat ι p)

/-- The induced map of actual residue fields. -/
def completedPolynomialResidueMap :
    ResidueField (ParameterLocalization.Ring R ι p) →+*
      ResidueField (CompletedRing R ι p) :=
  ResidueField.map (completedPolynomialMap R ι p)

@[simp] theorem completedPolynomialResidueMap_polynomial (f : MvPolynomial ι R) :
    completedResidueFieldEquiv R ι p
      (completedPolynomialResidueMap R ι p
        (residue (ParameterLocalization.Ring R ι p)
          (algebraMap (MvPolynomial ι R) (ParameterLocalization.Ring R ι p) f))) =
      algebraMap (MvPowerSeries ι (ResidueField R))
        (FractionRing (MvPowerSeries ι (ResidueField R)))
          (MvPolynomial.map (residue R) f : MvPowerSeries ι (ResidueField R)) := by
  change completionResidueFractionEquiv R ι
    (residueFieldRingEquiv Rhat ι (algebraMap R Rhat p)
      (completedPolynomialResidueMap R ι p
        (residue (ParameterLocalization.Ring R ι p)
          (algebraMap (MvPolynomial ι R) (ParameterLocalization.Ring R ι p) f)))) = _
  rw [completedPolynomialResidueMap, ResidueField.map_residue,
    completedPolynomialMap_polynomial, residueFieldRingEquiv_series,
    completionResidueFractionEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    completionResidueSeriesEquiv_polynomial]

/-- The complete actual residue square is the canonical power-series fraction embedding. -/
theorem completedPolynomialResidueMap_fraction_square :
    (completedResidueFieldEquiv R ι p).toRingHom.comp
        ((completedPolynomialResidueMap R ι p).comp
          (ParameterLocalization.residueFieldRingEquiv R ι p).symm.toRingHom) =
      canonicalResidueFractionMap R ι := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial ι (ResidueField R)))
  apply RingHom.ext
  intro f
  obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective (residue R) residue_surjective f
  change completedResidueFieldEquiv R ι p
      (completedPolynomialResidueMap R ι p
        ((ParameterLocalization.residueFieldRingEquiv R ι p).symm
          (algebraMap _ (FractionRing (MvPolynomial ι (ResidueField R)))
            (MvPolynomial.map (residue R) f)))) = _
  rw [← ParameterLocalization.residueFieldRingEquiv_polynomial R ι p f,
    RingEquiv.symm_apply_apply, completedPolynomialResidueMap_polynomial,
    RingHom.comp_apply, canonicalResidueFractionMap_polynomial]

end PowerSeriesLocalization
