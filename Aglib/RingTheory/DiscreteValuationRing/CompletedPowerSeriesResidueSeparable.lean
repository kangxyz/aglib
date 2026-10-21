/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.SeparablyGenerated.Equivalence
public import Aglib.RingTheory.DiscreteValuationRing.CompletedPowerSeriesPair

/-!
# General separability of the actual completed-series DVR residue map

The actual residue-field action is induced by the actual local map from the
polynomial coefficient-uniformizer localization to the completed power-series
coefficient-uniformizer localization. Its general separability follows from the
proved complete residue square and arbitrary-field power-series separability.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace PowerSeriesLocalization

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type*) [Finite ι] (p : R) [Fact (Irreducible p)]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "A" => ParameterLocalization.Ring R ι p
local notation "S" => CompletedRing R ι p

local instance : IsDomain (MvPowerSeries ι (ResidueField R)) :=
  NoZeroDivisors.to_isDomain _

/-- The actual completed-series map preserves the original uniformizer. -/
theorem completedPolynomialMap_uniformizer :
    completedPolynomialMap R ι p (algebraMap R A p) =
      algebraMap Rhat S (algebraMap R Rhat p) := by
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial ι R) A,
    completedPolynomialMap_polynomial]
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.map_C, MvPolynomial.coe_C]
  simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
    (IsScalarTower.algebraMap_apply Rhat (MvPowerSeries ι Rhat) S
      (algebraMap R Rhat p)).symm

/-- The actual residue-field action is generally separable, including imperfect residue fields. -/
theorem isTranscendentalSeparable_completedPolynomialResidueMap :
    let := (completedPolynomialResidueMap R ι p).toAlgebra
    Algebra.IsTranscendentalSeparable (ResidueField A) (ResidueField S) := by
  let : Algebra (ResidueField A) (ResidueField S) :=
    (completedPolynomialResidueMap R ι p).toAlgebra
  let F := FractionRing (MvPolynomial ι (ResidueField R))
  let L := FractionRing (MvPowerSeries ι (ResidueField R))
  let := MvPowerSeries.fractionFieldAlgebra (ResidueField R) ι
  let : Algebra.IsTranscendentalSeparable F L :=
    MvPowerSeries.isTranscendentalSeparable_fractionRing (ResidueField R) ι
  apply Algebra.isTranscendentalSeparable_of_ringEquivs
    (ParameterLocalization.residueFieldRingEquiv R ι p).symm
    (completedResidueFieldEquiv R ι p).symm
  apply RingHom.ext
  intro x
  apply (completedResidueFieldEquiv R ι p).injective
  change completedResidueFieldEquiv R ι p
      (completedPolynomialResidueMap R ι p
        ((ParameterLocalization.residueFieldRingEquiv R ι p).symm x)) =
    completedResidueFieldEquiv R ι p
      ((completedResidueFieldEquiv R ι p).symm (canonicalResidueFractionMap R ι x))
  rw [RingEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (completedPolynomialResidueMap_fraction_square R ι p) x

end PowerSeriesLocalization
