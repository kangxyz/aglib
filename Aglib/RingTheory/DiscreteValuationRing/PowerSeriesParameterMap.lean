/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterResidue
public import Aglib.RingTheory.DiscreteValuationRing.PowerSeriesLocalization
public import Aglib.RingTheory.MvPowerSeries.FractionFieldSeparable

/-!
# The actual map from polynomial to power-series uniformizer localizations

The residue map is identified with the canonical rational-function embedding into
the fraction field of power series. All comparisons use the native localization
and residue maps.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace PowerSeriesLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v) (p : R) [Fact (Irreducible p)]

local instance : IsDomain (MvPowerSeries ι R) :=
  NoZeroDivisors.to_isDomain _

local instance : IsDomain (MvPowerSeries ι (ResidueField R)) :=
  NoZeroDivisors.to_isDomain _

local notation "P" => MvPolynomial ι R
local notation "C" => MvPowerSeries ι R
local notation "A" => ParameterLocalization.Ring R ι p
local notation "S" => Ring R ι p

/-- Polynomial inclusion commutes with literal coefficient reduction. -/
theorem map_residue_polynomial (f : P) :
    MvPowerSeries.map (residue R) (f : C) =
      (MvPolynomial.map (residue R) f : MvPowerSeries ι (ResidueField R)) := by
  have h : (MvPowerSeries.map (residue R)).comp
      (MvPolynomial.coeToMvPowerSeries.ringHom : P →+* C) =
      (MvPolynomial.coeToMvPowerSeries.ringHom :
        MvPolynomial ι (ResidueField R) →+* MvPowerSeries ι (ResidueField R)).comp
          (MvPolynomial.map (residue R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp
  exact DFunLike.congr_fun h f

/-- The inverse image of the power-series coefficient prime is the polynomial coefficient prime. -/
theorem comap_coefficientIdeal :
    ParameterLocalization.parameterIdeal R ι p =
      (coefficientIdeal R ι p).comap
        (MvPolynomial.coeToMvPowerSeries.ringHom : P →+* C) := by
  ext f
  rw [← ParameterLocalization.ker_map_residue R ι p,
    ← ker_map_residue R ι p (Fact.out : Irreducible p)]
  change MvPolynomial.map (residue R) f = 0 ↔
    MvPowerSeries.map (residue R) (f : C) = 0
  rw [map_residue_polynomial]
  exact MvPolynomial.coe_eq_zero_iff.symm

/-- The canonical map between the actual two uniformizer localizations. -/
def polynomialMap : A →+* S :=
  Localization.localRingHom (ParameterLocalization.parameterIdeal R ι p)
    (coefficientIdeal R ι p) MvPolynomial.coeToMvPowerSeries.ringHom
    (comap_coefficientIdeal R ι p)

instance polynomialMap_isLocalHom : IsLocalHom (polynomialMap R ι p) :=
  Localization.isLocalHom_localRingHom _ _ _ _

@[simp] theorem polynomialMap_polynomial (f : P) :
    polynomialMap R ι p (algebraMap P A f) = algebraMap C S (f : C) :=
  Localization.localRingHom_to_map _ _ _ _ f

/-- The same original uniformizer is preserved by the actual map. -/
@[simp] theorem polynomialMap_uniformizer :
    polynomialMap R ι p (algebraMap R A p) = algebraMap R S p := by
  rw [IsScalarTower.algebraMap_apply R P A, polynomialMap_polynomial,
    IsScalarTower.algebraMap_apply R C S]
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.coe_C,
    MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- The original localized map is injective. -/
theorem polynomialMap_injective [Finite ι] : Function.Injective (polynomialMap R ι p) := by
  let : IsDiscreteValuationRing A := ParameterLocalization.isDiscreteValuationRing R ι p
  let : IsDiscreteValuationRing S := isDiscreteValuationRing R ι p
  apply IsDiscreteValuationRing.injective_of_map_irreducible (polynomialMap R ι p)
    (ParameterLocalization.uniformizer_irreducible R ι p)
  rw [polynomialMap_uniformizer]
  exact uniformizer_irreducible R ι p

/-- The actual induced map between the literal residue fields. -/
def polynomialResidueMap : ResidueField A →+* ResidueField S :=
  ResidueField.map (polynomialMap R ι p)

@[simp] theorem polynomialResidueMap_polynomial (f : P) :
    residueFieldRingEquiv R ι p
      (polynomialResidueMap R ι p (residue A (algebraMap P A f))) =
      algebraMap (MvPowerSeries ι (ResidueField R))
        (FractionRing (MvPowerSeries ι (ResidueField R)))
          (MvPolynomial.map (residue R) f : MvPowerSeries ι (ResidueField R)) := by
  rw [polynomialResidueMap, ResidueField.map_residue, polynomialMap_polynomial,
    residueFieldRingEquiv_series, map_residue_polynomial]

/-- Canonical fraction-field lifting of the polynomial inclusion, with no chosen field embedding. -/
abbrev canonicalResidueFractionMap :
    FractionRing (MvPolynomial ι (ResidueField R)) →+*
      FractionRing (MvPowerSeries ι (ResidueField R)) := by
  let := MvPowerSeries.fractionFieldAlgebra (ResidueField R) ι
  exact algebraMap _ _

@[simp] theorem canonicalResidueFractionMap_polynomial
    (f : MvPolynomial ι (ResidueField R)) :
    canonicalResidueFractionMap R ι
        (algebraMap _ (FractionRing (MvPolynomial ι (ResidueField R))) f) =
      algebraMap (MvPowerSeries ι (ResidueField R))
        (FractionRing (MvPowerSeries ι (ResidueField R)))
          (f : MvPowerSeries ι (ResidueField R)) := by
  let := MvPowerSeries.faithfulSMul_mvPolynomial (ResidueField R) ι
  let := MvPowerSeries.fractionFieldAlgebra (ResidueField R) ι
  let : IsScalarTower (MvPolynomial ι (ResidueField R))
      (FractionRing (MvPolynomial ι (ResidueField R)))
      (FractionRing (MvPowerSeries ι (ResidueField R))) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  change algebraMap _ (FractionRing (MvPowerSeries ι (ResidueField R)))
    (algebraMap _ (FractionRing (MvPolynomial ι (ResidueField R))) f) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact IsScalarTower.algebraMap_apply (MvPolynomial ι (ResidueField R))
    (MvPowerSeries ι (ResidueField R)) _ f

/-- The complete residue square identifies the actual map with the canonical fraction-field lift. -/
theorem polynomialResidueMap_fraction_square :
    (residueFieldRingEquiv R ι p).toRingHom.comp
        ((polynomialResidueMap R ι p).comp
          (ParameterLocalization.residueFieldRingEquiv R ι p).symm.toRingHom) =
      canonicalResidueFractionMap R ι := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial ι (ResidueField R)))
  apply RingHom.ext
  intro f
  obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective (residue R) residue_surjective f
  change residueFieldRingEquiv R ι p
      (polynomialResidueMap R ι p
        ((ParameterLocalization.residueFieldRingEquiv R ι p).symm
          (algebraMap _ (FractionRing (MvPolynomial ι (ResidueField R)))
            (MvPolynomial.map (residue R) f)))) = _
  rw [← ParameterLocalization.residueFieldRingEquiv_polynomial R ι p f,
    RingEquiv.symm_apply_apply, polynomialResidueMap_polynomial,
    RingHom.comp_apply, canonicalResidueFractionMap_polynomial]

end PowerSeriesLocalization
