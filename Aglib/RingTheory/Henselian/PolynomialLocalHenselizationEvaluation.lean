/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationSquare
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial evaluation in the higher actual henselization

The polynomial variable maps to the original last coordinate, while coefficients
use the actual lower-variable inclusion. Formal evaluation agrees with mapping
the coefficients and then embedding the polynomial into power series.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace PolynomialLocalHenselization

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The original last polynomial variable, viewed in the actual henselization. -/
def pivot (n : ℕ) : PolynomialLocalHenselization R (n + 1) :=
  algebraMap (PolynomialLocalRing R (n + 1)) (PolynomialLocalHenselization R (n + 1))
    (algebraMap (MvPolynomial (Fin (n + 1)) R) (PolynomialLocalRing R (n + 1))
      (MvPolynomial.X (Fin.last n)))

/-- Evaluate lower-henselization polynomials in the higher actual henselization. -/
def polynomialEvaluation (n : ℕ) :
    Polynomial (PolynomialLocalHenselization R n) →ₐ[R] PolynomialLocalHenselization R (n + 1) :=
  Polynomial.eval₂AlgHom (variableInclusion R n) (pivot R n) (fun _ => Commute.all _ _)

@[simp] theorem polynomialEvaluation_C (n : ℕ) (a : PolynomialLocalHenselization R n) :
    polynomialEvaluation R n (Polynomial.C a) = variableInclusion R n a := by
  exact Polynomial.eval₂_C _ _

@[simp] theorem polynomialEvaluation_X (n : ℕ) :
    polynomialEvaluation R n Polynomial.X = pivot R n := by
  exact Polynomial.eval₂_X _ _

variable [IsNoetherianRing R]

/-- Formal evaluation with the last variable isolated as the power-series variable. -/
def iteratedFormalMap (n : ℕ) : PolynomialLocalHenselization R (n + 1) →ₐ[R]
    PowerSeries (PolynomialLocalRing.FormalSeries R n) :=
  ((MvPowerSeries.finLastEquiv
    (AdicCompletion (maximalIdeal R) R) n).restrictScalars R).toAlgHom.comp
     (toFormalSeries R (n + 1))

instance iteratedFormalMap_isLocalHom (n : ℕ) :
    IsLocalHom (iteratedFormalMap R n).toRingHom := by
  constructor
  intro x hx
  have h := hx.map (MvPowerSeries.finLastEquiv
    (AdicCompletion (maximalIdeal R) R) n).symm.toRingHom
  have h' : IsUnit (toFormalSeries R (n + 1) x) := by
    change IsUnit ((MvPowerSeries.finLastEquiv (AdicCompletion (maximalIdeal R) R) n).symm
      (MvPowerSeries.finLastEquiv (AdicCompletion (maximalIdeal R) R) n
        (toFormalSeries R (n + 1) x))) at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  exact IsLocalHom.map_nonunit (f := (toFormalSeries R (n + 1)).toRingHom) x h'

/-- The lower henselization maps to constant series in the actual iterated target. -/
theorem iteratedFormalMap_variableInclusion (n : ℕ) (a : PolynomialLocalHenselization R n) :
    iteratedFormalMap R n (variableInclusion R n a) = PowerSeries.C (toFormalSeries R n a) := by
  change MvPowerSeries.finLastEquiv (AdicCompletion (maximalIdeal R) R) n
    (toFormalSeries R (n + 1) (variableInclusion R n a)) = _
  rw [show toFormalSeries R (n + 1) (variableInclusion R n a) =
    PolynomialLocalRing.formalVariableInclusion R n (toFormalSeries R n a) from
      AlgHom.congr_fun (toFormalSeries_comp_variableInclusion R n) a]
  exact PolynomialLocalRing.finLastEquiv_formalVariableInclusion R n _

/-- The original last coordinate becomes the actual iterated power-series variable. -/
theorem iteratedFormalMap_pivot (n : ℕ) :
    iteratedFormalMap R n (pivot R n) = PowerSeries.X := by
  have h := AlgHom.congr_fun (toFormalSeries_comp_of R (n + 1))
    (algebraMap (MvPolynomial (Fin (n + 1)) R) (PolynomialLocalRing R (n + 1))
      (MvPolynomial.X (Fin.last n)))
  change MvPowerSeries.finLastEquiv (AdicCompletion (maximalIdeal R) R) n
    (toFormalSeries R (n + 1) (pivot R n)) = _
  rw [show toFormalSeries R (n + 1) (pivot R n) =
    PolynomialLocalRing.toFormalSeries R (n + 1)
      (algebraMap (MvPolynomial (Fin (n + 1)) R) (PolynomialLocalRing R (n + 1))
        (MvPolynomial.X (Fin.last n))) from h,
    PolynomialLocalRing.toFormalSeries_algebraMap]
  change MvPowerSeries.finLastEquiv (AdicCompletion (maximalIdeal R) R) n
    (MvPolynomial.aeval _ (MvPolynomial.X (Fin.last n))) = _
  rw [MvPolynomial.aeval_X]
  change MvPowerSeries.finSuccEquiv (AdicCompletion (maximalIdeal R) R) n
    (MvPowerSeries.rename (Equiv.swap 0 (Fin.last n)) (MvPowerSeries.X (Fin.last n))) = _
  rw [MvPowerSeries.rename_X, Equiv.swap_apply_right, MvPowerSeries.finSuccEquiv_X_zero]

/-- The literal polynomial square in the coercion-map form used by finite equation systems. -/
theorem iteratedFormalMap_comp_polynomialEvaluation (n : ℕ) :
    (iteratedFormalMap R n).toRingHom.comp (polynomialEvaluation R n).toRingHom =
      Polynomial.coeToPowerSeries.ringHom.comp
        (Polynomial.mapRingHom (toFormalSeries R n).toRingHom) := by
  apply Polynomial.ringHom_ext
  · intro a
    change iteratedFormalMap R n (polynomialEvaluation R n (Polynomial.C a)) =
      (((Polynomial.C a).map (toFormalSeries R n).toRingHom :
        Polynomial (PolynomialLocalRing.FormalSeries R n)) :
          PowerSeries (PolynomialLocalRing.FormalSeries R n))
    rw [polynomialEvaluation_C, iteratedFormalMap_variableInclusion,
      Polynomial.map_C, Polynomial.coe_C]
    rfl
  · change iteratedFormalMap R n (polynomialEvaluation R n Polynomial.X) =
      ((Polynomial.X.map (toFormalSeries R n).toRingHom :
        Polynomial (PolynomialLocalRing.FormalSeries R n)) :
          PowerSeries (PolynomialLocalRing.FormalSeries R n))
    rw [polynomialEvaluation_X, iteratedFormalMap_pivot, Polynomial.map_X, Polynomial.coe_X]

end PolynomialLocalHenselization
