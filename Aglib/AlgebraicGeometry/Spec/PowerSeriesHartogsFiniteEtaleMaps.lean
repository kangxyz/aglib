/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesHartogsOpen
public import Aglib.AlgebraicGeometry.Spec.AffineClosedRestriction
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.VectorBundleFaithfulness
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! # Finite-etale maps on power-series Hartogs opens

The original scalar and unit cone on a base-open neighbourhood give full
faithfulness of the actual zero-section restriction. No normality, domain,
locality or completeness assumption is imposed on the Noetherian coefficient
ring. This supplies maps, not finite-etale essential surjectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPowerSeries

namespace AlgebraicGeometry.Scheme

open Modules Modules.Coherent FiniteEtale
universe u

/-- Every original finite-etale map on the first variable-ideal thickening lifts. -/
theorem powerSeriesHartogsFiniteEtale_baseChange_full
    {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsNoetherianRing A]
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hUV : Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A)) ⁻¹ᵁ U ≤ V)
    (hV : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V = U) :
    (baseChange ((idealThickeningIdealSheaf V.ι (RingHom.ker
      (constantCoeff : MvPowerSeries σ A →+* A))) ^ 1).subschemeι).Full := by
  let : CompactSpace V := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact
      (V : Set (Spec (.of (MvPowerSeries σ A)))))
  let : V.toScheme.IsQuasiAffine := IsQuasiAffine.of_isImmersion V.ι
  obtain ⟨hunit⟩ := powerSeriesUnitSectionCone_isLimit_of_baseOpen_le U hU V hUV hV
  exact FiniteEtale.Adic.firstStage_baseChange_full_of_unitSectionCone _ hunit

/-- Equality of original finite-etale maps is detected on the first thickening. -/
theorem powerSeriesHartogsFiniteEtale_baseChange_faithful
    {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsNoetherianRing A]
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hUV : Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A)) ⁻¹ᵁ U ≤ V)
    (hV : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V = U) :
    (baseChange ((idealThickeningIdealSheaf V.ι (RingHom.ker
      (constantCoeff : MvPowerSeries σ A →+* A))) ^ 1).subschemeι).Faithful := by
  let : CompactSpace V := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact
      (V : Set (Spec (.of (MvPowerSeries σ A)))))
  let : V.toScheme.IsQuasiAffine := IsQuasiAffine.of_isImmersion V.ι
  obtain ⟨hunit⟩ := powerSeriesUnitSectionCone_isLimit_of_baseOpen_le U hU V hUV hV
  exact FiniteEtale.Adic.firstStage_baseChange_faithful_of_unitSectionCone _ hunit

/-- The actual first-stage functor is fully faithful, with no assumed completion property. -/
def powerSeriesHartogsFiniteEtale_fullyFaithful
    {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsNoetherianRing A]
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hUV : Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A)) ⁻¹ᵁ U ≤ V)
    (hV : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V = U) :
    (baseChange ((idealThickeningIdealSheaf V.ι (RingHom.ker
      (constantCoeff : MvPowerSeries σ A →+* A))) ^ 1).subschemeι).FullyFaithful := by
  let := powerSeriesHartogsFiniteEtale_baseChange_full U hU V hUV hV
  let := powerSeriesHartogsFiniteEtale_baseChange_faithful U hU V hUV hV
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- Restriction along the actual zero-section map is fully faithful on finite-etale covers. -/
def powerSeriesHartogsFiniteEtale_zeroSection_fullyFaithful
    {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsNoetherianRing A]
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hUV : Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A)) ⁻¹ᵁ U ≤ V)
    (hV : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V = U) :
    (baseChange (Spec.map (CommRingCat.ofHom
      (constantCoeff : MvPowerSeries σ A →+* A)) ∣_ V)).FullyFaithful := by
  let K := idealThickeningIdealSheaf V.ι (RingHom.ker
    (constantCoeff : MvPowerSeries σ A →+* A))
  have hK : (baseChange K.subschemeι).FullyFaithful := by
    have hp : (baseChange (K ^ 1).subschemeι).FullyFaithful :=
      powerSeriesHartogsFiniteEtale_fullyFaithful U hU V hUV hV
    exact Eq.mp (congrArg
      (fun J : V.toScheme.IdealSheafData => (baseChange J.subschemeι).FullyFaithful)
      (pow_one K)) hp
  have hs : Function.Surjective (constantCoeff : MvPowerSeries σ A →+* A) :=
    fun a => ⟨C a, by simp⟩
  let e := affineClosedRestrictionIso
    (constantCoeff : MvPowerSeries σ A →+* A) V hs
  let : (baseChange e.hom).Full := baseChange_full_of_isIso e.hom
  let : (baseChange e.hom).Faithful := baseChange_faithful_of_isIso e.hom
  have hh := (hK.comp (Functor.FullyFaithful.ofFullyFaithful (baseChange e.hom))).ofIso
    (baseChangeComp K.subschemeι e.hom).symm
  exact hh.ofIso (eqToIso (congrArg baseChange
    (affineClosedRestrictionIso_hom_ι
      (constantCoeff : MvPowerSeries σ A →+* A) V hs)))

end AlgebraicGeometry.Scheme
