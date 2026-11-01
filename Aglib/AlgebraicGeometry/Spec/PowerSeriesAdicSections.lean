/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.SplitAdicSections
public import Aglib.RingTheory.MvPowerSeries.QuotientCoefficients
public import Aglib.RingTheory.MvPowerSeries.VariableIdeal
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! # Scalar extension on arbitrary power-series opens

Quotient flatness and completeness are derived for the original variable ideal.
The coefficient ring is not assumed complete, and the ambient open need not
be the inverse image of its zero-section intersection.
-/

@[expose] public noncomputable section

open CategoryTheory MvPowerSeries

namespace AlgebraicGeometry.Scheme

universe u
variable {σ : Type} {A : Type u} [Finite σ] [CommRing A]

/-- Original quotient scalars are flat because their native coefficient basis
is finite free, including the zeroth quotient. -/
theorem powerSeriesKernelQuotient_flat (n : ℕ) :
    ((Ideal.Quotient.mk ((RingHom.ker
      (constantCoeff : MvPowerSeries σ A →+* A)) ^ n)).comp
      (C : A →+* MvPowerSeries σ A)).Flat := by
  rw [← span_X_eq_ker_constantCoeff (σ := σ) (R := A)]
  change (algebraMap A (MvPowerSeries σ A ⧸
    (Ideal.span (Set.range (X : σ → MvPowerSeries σ A))) ^ n)).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

/-- Native variable-ideal completeness, expressed at its original augmentation kernel. -/
theorem powerSeriesKernel_isAdicComplete :
    IsAdicComplete (RingHom.ker (constantCoeff : MvPowerSeries σ A →+* A))
      (MvPowerSeries σ A) := by
  rw [← span_X_eq_ker_constantCoeff (σ := σ) (R := A)]
  infer_instance

variable (V : (Spec (.of (MvPowerSeries σ A))).Opens)
variable [QuasiCompact (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V).ι]
  [QuasiSeparated (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V).ι]
  (hU : Function.Bijective (hartogsScalarMap A
    (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V)))

include V hU in
omit [Finite σ]
  [QuasiCompact (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V).ι]
  [QuasiSeparated (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V).ι] in
/-- Scalar bijectivity on the original zero-section open, in native global
section coordinates. -/
theorem powerSeriesZeroOpenScalar_bijective : Function.Bijective (affineScalarMap
      (splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V).ι) := by
  let U := splitSectionOpen (constantCoeff : MvPowerSeries σ A →+* A) V
  rw [← affineScalarMap_topIso U] at hU
  exact Function.Bijective.of_comp_left
    (f := U.topIso.hom.hom) (g := affineScalarMap U.ι) hU
    (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective

include V hU in
/-- Every original kernel-power thickening has its native scalar isomorphism. -/
theorem powerSeriesAdicSectionScalar_bijective (n : ℕ) :
    Function.Bijective (adicSectionScalar V.ι
      (RingHom.ker (constantCoeff : MvPowerSeries σ A →+* A)) n) := by
  have hu := powerSeriesZeroOpenScalar_bijective V hU
  exact splitAdicSectionScalar_bijective (C : A →+* MvPowerSeries σ A)
    (constantCoeff : MvPowerSeries σ A →+* A) constantCoeff_comp_C V hu
    powerSeriesKernelQuotient_flat n

/-- The constructed map from the original ambient open into the original
power-series ring. No map into an alternative completion is selected. -/
def powerSeriesAdicSectionsRetraction :
    Γ(Spec (.of (MvPowerSeries σ A)), V) →+* MvPowerSeries σ A := by
  let := powerSeriesKernel_isAdicComplete (σ := σ) (A := A)
  exact splitAdicSectionsRetraction (C : A →+* MvPowerSeries σ A)
    (constantCoeff : MvPowerSeries σ A →+* A) constantCoeff_comp_C V
    (powerSeriesZeroOpenScalar_bijective V hU) powerSeriesKernelQuotient_flat

/-- The constructed map retracts the actual ambient scalar restriction. -/
theorem powerSeriesAdicSectionsRetraction_scalar :
    (powerSeriesAdicSectionsRetraction V hU).comp
      (hartogsScalarMap (MvPowerSeries σ A) V) = RingHom.id (MvPowerSeries σ A) := by
  let := powerSeriesKernel_isAdicComplete (σ := σ) (A := A)
  exact splitAdicSectionsRetraction_scalar (C : A →+* MvPowerSeries σ A)
    (constantCoeff : MvPowerSeries σ A →+* A) constantCoeff_comp_C V
    (powerSeriesZeroOpenScalar_bijective V hU) powerSeriesKernelQuotient_flat

include V hU in
/-- The scalar restriction is bijective on an arbitrary nonempty ambient open
whose original zero-section restriction is bijective. -/
theorem powerSeriesAdicSections_bijective [IsDomain A] [Nonempty V] :
    Function.Bijective (hartogsScalarMap (MvPowerSeries σ A) V) := by
  let : IsDomain (MvPowerSeries σ A) := NoZeroDivisors.to_isDomain _
  exact hartogsScalarMap_bijective_of_retraction (MvPowerSeries σ A) V
    (powerSeriesAdicSectionsRetraction V hU) (powerSeriesAdicSectionsRetraction_scalar V hU)

include V hU in
/-- Original ambient scalar bijectivity in native scheme-top coordinates. -/
theorem powerSeriesAffineScalar_bijective [IsDomain A] [Nonempty V] :
    Function.Bijective (affineScalarMap V.ι) := by
  have h := powerSeriesAdicSections_bijective V hU
  rw [← affineScalarMap_topIso V] at h
  exact Function.Bijective.of_comp_left
    (f := V.topIso.hom.hom) (g := affineScalarMap V.ι) h
    (ConcreteCategory.bijective_of_isIso V.topIso.hom).injective

/-- Full scalar equivalence, with the constructed direct retraction as inverse. -/
def powerSeriesAdicSectionsEquiv [IsDomain A] [Nonempty V] :
    MvPowerSeries σ A ≃+* Γ(Spec (.of (MvPowerSeries σ A)), V) := by
  let : IsDomain (MvPowerSeries σ A) := NoZeroDivisors.to_isDomain _
  exact splitSectionsEquiv (MvPowerSeries σ A) V (powerSeriesAdicSectionsRetraction V hU)
    (powerSeriesAdicSectionsRetraction_scalar V hU)

end AlgebraicGeometry.Scheme
