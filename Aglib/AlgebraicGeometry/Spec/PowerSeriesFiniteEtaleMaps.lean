/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesUnitSectionCone
public import Aglib.AlgebraicGeometry.Spec.AffineClosedRestriction
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.VectorBundleFaithfulness
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! # Original finite-etale maps on punctured power-series neighbourhoods

The normal local Hartogs theorem constructs the scalar section limit on the
original ambient open. Finite locally free cover algebras then lift actual
first-stage cover maps. No coherent-completion fullness or coefficient-ring
completeness is assumed, and the ambient open is not replaced by a pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPowerSeries

namespace AlgebraicGeometry.Scheme

open Modules Modules.Coherent FiniteEtale
universe u

/-- Every original finite-etale map on the first variable-ideal thickening lifts. -/
theorem powerSeriesPuncturedFiniteEtale_baseChange_full
    {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hdim : 2 ≤ ringKrullDim A)
    (hV : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V =
      puncturedSpecOpen A) :
    (baseChange ((idealThickeningIdealSheaf V.ι (RingHom.ker
      (constantCoeff : MvPowerSeries σ A →+* A))) ^ 1).subschemeι).Full := by
  let : CompactSpace V := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact
      (V : Set (Spec (.of (MvPowerSeries σ A)))))
  let : V.toScheme.IsQuasiAffine := IsQuasiAffine.of_isImmersion V.ι
  obtain ⟨hunit⟩ := powerSeriesPuncturedUnitSectionCone_isLimit V hdim hV
  exact FiniteEtale.Adic.firstStage_baseChange_full_of_unitSectionCone _ hunit

/-- Equality of original finite-etale maps is detected on the first thickening. -/
theorem powerSeriesPuncturedFiniteEtale_baseChange_faithful
    {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hdim : 2 ≤ ringKrullDim A)
    (hV : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V =
      puncturedSpecOpen A) :
    (baseChange ((idealThickeningIdealSheaf V.ι (RingHom.ker
      (constantCoeff : MvPowerSeries σ A →+* A))) ^ 1).subschemeι).Faithful := by
  let : CompactSpace V := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact
      (V : Set (Spec (.of (MvPowerSeries σ A)))))
  let : V.toScheme.IsQuasiAffine := IsQuasiAffine.of_isImmersion V.ι
  obtain ⟨hunit⟩ := powerSeriesPuncturedUnitSectionCone_isLimit V hdim hV
  exact FiniteEtale.Adic.firstStage_baseChange_faithful_of_unitSectionCone _ hunit

/-- The actual first-stage functor is fully faithful, with no assumed completion property. -/
def powerSeriesPuncturedFiniteEtaleFullyFaithful
    {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hdim : 2 ≤ ringKrullDim A)
    (hV : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V =
      puncturedSpecOpen A) :
    (baseChange ((idealThickeningIdealSheaf V.ι (RingHom.ker
      (constantCoeff : MvPowerSeries σ A →+* A))) ^ 1).subschemeι).FullyFaithful := by
  let := powerSeriesPuncturedFiniteEtale_baseChange_full V hdim hV
  let := powerSeriesPuncturedFiniteEtale_baseChange_faithful V hdim hV
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- Restriction along the actual zero-section map is fully faithful on finite-etale covers. -/
def powerSeriesPuncturedFiniteEtaleZeroSectionFullyFaithful
    {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hdim : 2 ≤ ringKrullDim A)
    (hV : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V =
      puncturedSpecOpen A) :
    (baseChange (Spec.map (CommRingCat.ofHom
      (constantCoeff : MvPowerSeries σ A →+* A)) ∣_ V)).FullyFaithful := by
  let K := idealThickeningIdealSheaf V.ι (RingHom.ker
    (constantCoeff : MvPowerSeries σ A →+* A))
  have hK : (baseChange K.subschemeι).FullyFaithful := by
    have hp : (baseChange (K ^ 1).subschemeι).FullyFaithful :=
      powerSeriesPuncturedFiniteEtaleFullyFaithful V hdim hV
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
