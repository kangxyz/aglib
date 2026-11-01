/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesAdicSections
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.UnitSectionLimit
public import Aglib.AlgebraicGeometry.FunctionField.HartogsSections
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # The actual unit cone on punctured power-series neighbourhoods

Native variable-ideal completeness, the constructed scalar retraction and the
original quotient-section comparisons supply the actual module-unit cone.
The punctured normal-base specialization constructs its Hartogs input; it
assumes neither completeness of the coefficient ring nor that the ambient
open is the inverse image of its zero-section intersection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPowerSeries

namespace AlgebraicGeometry.Scheme

open Modules Modules.Coherent
universe u

variable {σ : Type} [Finite σ] {A : Type u} [CommRing A] [IsDomain A]
  (V : (Spec (.of (MvPowerSeries σ A))).Opens)

/-- The constructed original unit-section cone on an arbitrary nonempty power-series open. -/
theorem powerSeriesUnitSectionCone_isLimit [Nonempty V]
    [QuasiCompact (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V).ι]
    [QuasiSeparated (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V).ι]
    (hU : Function.Bijective (hartogsScalarMap A
      (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V))) :
    Nonempty (IsLimit (idealSheafSectionCone V
      (idealThickeningIdealSheaf V.ι (RingHom.ker
        (constantCoeff : MvPowerSeries σ A →+* A)))
      (SheafOfModules.unit V.toScheme.ringCatSheaf))) := by
  let := powerSeriesKernel_isAdicComplete (σ := σ) (A := A)
  have hb := powerSeriesAdicSectionScalar_bijective V hU
  have hA := powerSeriesAffineScalar_bijective V hU
  exact idealSheafUnitSectionCone_isLimit_of_adicScalars V.ι _ hb hA

/-- Normal Noetherian local dimension at least two supplies the actual punctured input. -/
theorem powerSeriesPuncturedUnitSectionCone_isLimit
    [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A)
    (hV : splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V =
      puncturedSpecOpen A) :
    Nonempty (IsLimit (idealSheafSectionCone V
      (idealThickeningIdealSheaf V.ι (RingHom.ker
        (constantCoeff : MvPowerSeries σ A →+* A)))
      (SheafOfModules.unit V.toScheme.ringCatSheaf))) := by
  have hU : Nonempty (splitSectionOpen
      (constantCoeff : MvPowerSeries σ A →+* A) V) := by
    rw [hV]
    exact puncturedSpecOpen_nonempty A hdim
  let : Nonempty V := by
    obtain ⟨x⟩ := hU
    exact ⟨⟨(Spec.map (CommRingCat.ofHom
      (constantCoeff : MvPowerSeries σ A →+* A))) x.val, x.property⟩⟩
  have hs : Function.Bijective (hartogsScalarMap A
      (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V)) := by
    rw [hV]
    exact puncturedSpecScalarMap_bijective A hdim
  exact powerSeriesUnitSectionCone_isLimit V hs

end AlgebraicGeometry.Scheme
