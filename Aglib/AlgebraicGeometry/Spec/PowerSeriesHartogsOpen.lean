/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsOpenEnlargement
public import Aglib.AlgebraicGeometry.Spec.PowerSeriesAdicSections
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.UnitSectionLimit
public import Aglib.RingTheory.MvPowerSeries.Flat

/-! # Hartogs scalar and unit cone on power-series neighbourhoods

The ambient open contains the actual inverse image of a quasi-compact Hartogs
open of the coefficient spectrum. Flat base change and the original
quasicoherent unit give the scalar comparison without any domain assumption.
Together with the literal zero-section intersection this constructs the
original unit-section cone; it does not assert finite-etale effectivity.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MvPowerSeries

namespace AlgebraicGeometry.Scheme

universe u
variable {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The actual scalar on a power-series open containing a base Hartogs open
is bijective, also for nonreduced and nondomain coefficient rings. -/
theorem powerSeriesAffineScalar_bijective_of_baseOpen_le
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hUV : Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A)) ⁻¹ᵁ U ≤ V) :
    Function.Bijective (affineScalarMap V.ι) := by
  let c := Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A))
  have hflat : (C : A →+* MvPowerSeries σ A).Flat := by
    change (algebraMap A (MvPowerSeries σ A)).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact MvPowerSeries.flat_of_isNoetherian σ A
  have h := Cohomology.scalarSections_bijective_of_flat_of_isPullback
    (c ∣_ U) (C : A →+* MvPowerSeries σ A) (c ⁻¹ᵁ U).ι U.ι
    (isPullback_morphismRestrict c U) hflat hU
  exact affineScalarMap_bijective_of_hartogs_open_le
    (MvPowerSeries σ A) (c ⁻¹ᵁ U) V hUV h

/-- Both original zero-section and ambient scalars give the original
module-unit completion cone. The coefficient ring need not be a domain. -/
theorem powerSeriesUnitSectionCone_isLimit_of_baseOpen_le
    (U : (Spec (.of A)).Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι))
    (V : (Spec (.of (MvPowerSeries σ A))).Opens)
    (hUV : Spec.map (CommRingCat.ofHom (C : A →+* MvPowerSeries σ A)) ⁻¹ᵁ U ≤ V)
    (hzero : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V = U) :
    Nonempty (IsLimit (Modules.Coherent.idealSheafSectionCone V
      (Modules.idealThickeningIdealSheaf V.ι
        (RingHom.ker (constantCoeff : MvPowerSeries σ A →+* A)))
      (SheafOfModules.unit V.toScheme.ringCatSheaf))) := by
  let := powerSeriesKernel_isAdicComplete (σ := σ) (A := A)
  have hbase : Function.Bijective (hartogsScalarMap A
      (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V)) := by
    rw [hzero, ← affineScalarMap_topIso U]
    exact (ConcreteCategory.bijective_of_isIso U.topIso.hom).comp hU
  let : QuasiCompact
      (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V).ι := by
    rw [hzero]
    infer_instance
  let : QuasiSeparated
      (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V).ι := by
    rw [hzero]
    infer_instance
  exact Modules.Coherent.idealSheafUnitSectionCone_isLimit_of_adicScalars V.ι _
    (powerSeriesAdicSectionScalar_bijective V hbase)
    (powerSeriesAffineScalar_bijective_of_baseOpen_le U hU V hUV)

end AlgebraicGeometry.Scheme
