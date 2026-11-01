/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesHartogsFiniteEtaleMaps
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.SectionRecovery

/-! # Original cover recovery on the inverse-image Hartogs open

The zero section and coefficient projection restrict to the original base
open, using only the canonical isomorphism of equal opens. Full faithfulness
on that section recovers the actual finite-etale cover as the geometric
pullback of its actual section restriction. No global-section algebra is
assumed etale, and the larger ambient open is not replaced by this base open.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPowerSeries

namespace AlgebraicGeometry.Scheme

universe u
variable {σ : Type} {A : Type u} [CommRing A]

local notation "c" => Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A))
local notation "z" => Spec.map
  (CommRingCat.ofHom (constantCoeff : MvPowerSeries σ A →+* A))

/-- The original zero section is a section of the original coefficient map. -/
theorem powerSeriesZero_comp_coefficient : z ≫ c = 𝟙 (Spec (.of A)) := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((constantCoeff : MvPowerSeries σ A →+* A).comp C)) = _
  rw [constantCoeff_comp_C]
  exact Spec.map_id _

/-- The actual zero-section inverse image of the actual base-open inverse
image is the unchanged coefficient open. -/
theorem powerSeriesZero_preimage_baseOpen (U : (Spec (.of A)).Opens) :
    z ⁻¹ᵁ (c ⁻¹ᵁ U) = U := by
  rw [← Hom.comp_preimage, powerSeriesZero_comp_coefficient]
  rfl

/-- The actual restricted zero section, with its source identified by the
canonical isomorphism of equal opens. -/
def powerSeriesBaseOpenSection (U : (Spec (.of A)).Opens) :
    U.toScheme ⟶ (c ⁻¹ᵁ U).toScheme :=
  ((Spec (.of A)).isoOfEq (powerSeriesZero_preimage_baseOpen (σ := σ) U)).inv ≫
    (z ∣_ (c ⁻¹ᵁ U))

/-- Its original composite into the power-series spectrum. -/
@[reassoc]
theorem powerSeriesBaseOpenSection_ι (U : (Spec (.of A)).Opens) :
    powerSeriesBaseOpenSection (σ := σ) U ≫ (c ⁻¹ᵁ U).ι = U.ι ≫ z := by
  simp only [powerSeriesBaseOpenSection, Category.assoc, morphismRestrict_ι,
    isoOfEq_inv_ι_assoc]

/-- The two original restricted maps still form a section and retraction. -/
theorem powerSeriesBaseOpenSection_retraction (U : (Spec (.of A)).Opens) :
    powerSeriesBaseOpenSection (σ := σ) U ≫ (c ∣_ U) = 𝟙 U.toScheme := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    powerSeriesBaseOpenSection_ι, Category.assoc, powerSeriesZero_comp_coefficient]
  simp

/-- Full faithfulness on the actual restricted section follows from the
proved nondomain Hartogs unit cone and the canonical source isomorphism. -/
def powerSeriesBaseOpenSectionFullyFaithful [Finite σ] [IsNoetherianRing A]
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι)) :
    (FiniteEtale.baseChange (powerSeriesBaseOpenSection (σ := σ) U)).FullyFaithful := by
  let e := (Spec (.of A)).isoOfEq (powerSeriesZero_preimage_baseOpen (σ := σ) U)
  have hz := powerSeriesHartogsFiniteEtaleZeroSectionFullyFaithful
    U hU (c ⁻¹ᵁ U) le_rfl (powerSeriesZero_preimage_baseOpen (σ := σ) U)
  let : (FiniteEtale.baseChange e.inv).Full := FiniteEtale.baseChange_full_of_isIso e.inv
  let : (FiniteEtale.baseChange e.inv).Faithful :=
    FiniteEtale.baseChange_faithful_of_isIso e.inv
  have hf := hz.comp (Functor.FullyFaithful.ofFullyFaithful (FiniteEtale.baseChange e.inv))
  exact hf.ofIso (FiniteEtale.baseChangeComp (z ∣_ (c ⁻¹ᵁ U)) e.inv).symm

/-- The original cover over the base-open inverse image is recovered from
its actual section cover. The candidate is a genuine geometric pullback. -/
def powerSeriesBaseOpenCoverRecovery [Finite σ] [IsNoetherianRing A]
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (D : FiniteEtale (c ⁻¹ᵁ U).toScheme) :
    D ≅ (FiniteEtale.baseChange (c ∣_ U)).obj
      ((FiniteEtale.baseChange (powerSeriesBaseOpenSection (σ := σ) U)).obj D) :=
  FiniteEtale.coverIsoOfFullyFaithfulSection
    (powerSeriesBaseOpenSection (σ := σ) U) (c ∣_ U)
    (powerSeriesBaseOpenSection_retraction (σ := σ) U)
    (powerSeriesBaseOpenSectionFullyFaithful (σ := σ) U hU) D

/-- Recovery preserves the prescribed original section comparison exactly. -/
@[simp]
theorem powerSeriesBaseOpenCoverRecovery_section_hom [Finite σ] [IsNoetherianRing A]
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (D : FiniteEtale (c ⁻¹ᵁ U).toScheme) :
    (FiniteEtale.baseChange (powerSeriesBaseOpenSection (σ := σ) U)).map
      (powerSeriesBaseOpenCoverRecovery U hU D).hom =
        (FiniteEtale.sectionRetractionComparison
          (powerSeriesBaseOpenSection (σ := σ) U) (c ∣_ U)
          (powerSeriesBaseOpenSection_retraction (σ := σ) U) D).inv :=
  FiniteEtale.coverIsoOfFullyFaithfulSection_map_hom _ _ _ _ _

/-- The original zero section into the larger open with its canonical source
identification, not a newly chosen section. -/
def powerSeriesAmbientOpenSection (U : (Spec (.of A)).Opens)
    (V : (Spec (.of (MvPowerSeries σ A))).Opens) (hzero : z ⁻¹ᵁ V = U) :
    U.toScheme ⟶ V.toScheme :=
  ((Spec (.of A)).isoOfEq hzero).inv ≫ (z ∣_ V)

@[reassoc]
theorem powerSeriesAmbientOpenSection_ι (U : (Spec (.of A)).Opens)
    (V : (Spec (.of (MvPowerSeries σ A))).Opens) (hzero : z ⁻¹ᵁ V = U) :
    powerSeriesAmbientOpenSection U V hzero ≫ V.ι = U.ι ≫ z := by
  simp only [powerSeriesAmbientOpenSection, Category.assoc, morphismRestrict_ι,
    isoOfEq_inv_ι_assoc]

/-- The base-open section and the ambient section agree through the actual
open inclusion. -/
theorem powerSeriesBaseOpenSection_homOfLE (U : (Spec (.of A)).Opens)
    (V : (Spec (.of (MvPowerSeries σ A))).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) :
    powerSeriesBaseOpenSection (σ := σ) U ≫
      (Spec (.of (MvPowerSeries σ A))).homOfLE hUV =
        powerSeriesAmbientOpenSection U V hzero := by
  apply (cancel_mono V.ι).mp
  rw [Category.assoc, homOfLE_ι, powerSeriesBaseOpenSection_ι,
    powerSeriesAmbientOpenSection_ι]

/-- The actual two restrictions of the original cover are compared by
native composition and the proved original section equation. -/
def powerSeriesSectionCoverComparison (U : (Spec (.of A)).Opens)
    (V : (Spec (.of (MvPowerSeries σ A))).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme) :
    (FiniteEtale.baseChange (powerSeriesBaseOpenSection (σ := σ) U)).obj
      ((FiniteEtale.baseChange
        ((Spec (.of (MvPowerSeries σ A))).homOfLE hUV)).obj D) ≅
      (FiniteEtale.baseChange (powerSeriesAmbientOpenSection U V hzero)).obj D :=
  (FiniteEtale.baseChangeComp
    ((Spec (.of (MvPowerSeries σ A))).homOfLE hUV)
    (powerSeriesBaseOpenSection (σ := σ) U)).symm.app D ≪≫
      (eqToIso (congrArg FiniteEtale.baseChange
        (powerSeriesBaseOpenSection_homOfLE U V hUV hzero))).app D

/-- Restricting the actual ambient cover to the base-open inverse image
recovers precisely the pullback of its original ambient zero-section cover.
This makes no claim that its global-section algebra is already etale. -/
def powerSeriesHartogsCoverRecovery [Finite σ] [IsNoetherianRing A]
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of (MvPowerSeries σ A))).Opens) (hUV : c ⁻¹ᵁ U ≤ V)
    (hzero : z ⁻¹ᵁ V = U) (D : FiniteEtale V.toScheme) :
    (FiniteEtale.baseChange
      ((Spec (.of (MvPowerSeries σ A))).homOfLE hUV)).obj D ≅
      (FiniteEtale.baseChange (c ∣_ U)).obj
        ((FiniteEtale.baseChange (powerSeriesAmbientOpenSection U V hzero)).obj D) :=
  powerSeriesBaseOpenCoverRecovery U hU _ ≪≫
    (FiniteEtale.baseChange (c ∣_ U)).mapIso
      (powerSeriesSectionCoverComparison U V hUV hzero D)

end AlgebraicGeometry.Scheme
