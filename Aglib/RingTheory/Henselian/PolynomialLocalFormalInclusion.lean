/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalFormal
public import Aglib.RingTheory.Henselian.PolynomialLocalFormalSquare

/-!
# The local polynomial square with actual formal variable inclusion

The formal inclusion is the constant-series inclusion transported through the
actual `finLastEquiv`. Thus its variables follow the explicit swap-based
embedding, and the original localized polynomial evaluations commute.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace PolynomialLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Inclusion of the lower formal variables in the actual `finLastEquiv` order. -/
def formalVariableInclusion (n : ℕ) : FormalSeries R n →ₐ[R] FormalSeries R (n + 1) :=
  ((MvPowerSeries.finLastEquiv
    (AdicCompletion (maximalIdeal R) R) n).symm.restrictScalars R).toAlgHom.comp
     (IsScalarTower.toAlgHom R (FormalSeries R n) (PowerSeries (FormalSeries R n)))

/-- Isolating the last variable turns the formal inclusion into constant series. -/
theorem finLastEquiv_formalVariableInclusion (n : ℕ) (f : FormalSeries R n) :
    MvPowerSeries.finLastEquiv (AdicCompletion (maximalIdeal R) R) n
      (formalVariableInclusion R n f) = PowerSeries.C f := by
  change MvPowerSeries.finLastEquiv (AdicCompletion (maximalIdeal R) R) n
    ((MvPowerSeries.finLastEquiv (AdicCompletion (maximalIdeal R) R) n).symm
      (PowerSeries.C f)) = _
  exact AlgEquiv.apply_symm_apply _ _

instance formalVariableInclusion_isLocalHom (n : ℕ) :
    IsLocalHom (formalVariableInclusion R n).toRingHom := by
  constructor
  intro f hf
  have h := hf.map (MvPowerSeries.finLastEquiv
    (AdicCompletion (maximalIdeal R) R) n).toRingHom
  change IsUnit (MvPowerSeries.finLastEquiv (AdicCompletion (maximalIdeal R) R) n
    (formalVariableInclusion R n f)) at h
  rw [finLastEquiv_formalVariableInclusion] at h
  simpa only [PowerSeries.constantCoeff_C] using h.map PowerSeries.constantCoeff

/-- The named formal map uses exactly the agreed lower-variable embedding. -/
theorem formalVariableInclusion_X (n : ℕ) (i : Fin n) :
    formalVariableInclusion R n (MvPowerSeries.X i) =
      MvPowerSeries.X (lowerVariableEmbedding n i) := by
  apply (MvPowerSeries.finLastEquiv (AdicCompletion (maximalIdeal R) R) n).injective
  rw [finLastEquiv_formalVariableInclusion,
    MvPowerSeries.finLastEquiv_X_lowerVariableEmbedding]

variable [IsNoetherianRing R]

/-- The original local polynomial square commutes as literal algebra maps. -/
theorem toFormalSeries_comp_variableInclusion (n : ℕ) :
    (toFormalSeries R (n + 1)).comp (variableInclusion R n) =
      (formalVariableInclusion R n).comp (toFormalSeries R n) := by
  apply IsLocalization.algHom_ext (originIdeal R n).primeCompl
  apply MvPolynomial.algHom_ext
  intro i
  change toFormalSeries R (n + 1)
    (variableInclusion R n (algebraMap (MvPolynomial (Fin n) R)
      (PolynomialLocalRing R n) (MvPolynomial.X i))) =
    formalVariableInclusion R n (toFormalSeries R n
      (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) (MvPolynomial.X i)))
  rw [variableInclusion_algebraMap, toFormalSeries_algebraMap,
    toFormalSeries_algebraMap, MvPolynomial.rename_X]
  change MvPolynomial.aeval _ (MvPolynomial.X _) =
    formalVariableInclusion R n (MvPolynomial.aeval _ (MvPolynomial.X i))
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, formalVariableInclusion_X]

end PolynomialLocalRing
