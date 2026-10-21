/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalRing
public import Aglib.RingTheory.MvPowerSeries.FinLastEquiv

/-!
# The actual lower-variable formal square

The swap-based polynomial inclusion becomes the constant-series inclusion under
`finLastEquiv`. This checks the coordinate convention needed by the polynomial
local henselization maps; it does not identify this embedding with `Fin.castSucc`.
-/

@[expose] public section

noncomputable section

namespace MvPowerSeries

variable (R : Type*) [CommRing R]

/-- Each actual lower variable becomes its same-index coefficient variable. -/
theorem finLastEquiv_X_lowerVariableEmbedding (n : ℕ) (i : Fin n) :
    finLastEquiv R n (X (PolynomialLocalRing.lowerVariableEmbedding n i)) =
      PowerSeries.C (X i) := by
  change finSuccEquiv R n
    (rename (Equiv.swap 0 (Fin.last n))
      (X (PolynomialLocalRing.lowerVariableEmbedding n i))) = _
  rw [rename_X, PolynomialLocalRing.lowerVariableEmbedding_apply,
    Equiv.swap_apply_self, finSuccEquiv_X_succ]

/-- Coefficient constants remain coefficient constants after isolating the last variable. -/
theorem finLastEquiv_C (n : ℕ) (r : R) :
    finLastEquiv R n (C r) = PowerSeries.C (C r) := by
  change finSuccEquiv R n (rename (Equiv.swap 0 (Fin.last n)) (C r)) = _
  rw [rename_C, finSuccEquiv_C]

/-- The original polynomial lower-variable inclusion commutes literally with
constant-series inclusion, in the actual `finLastEquiv` coordinate convention. -/
theorem finLastEquiv_rename_polynomial (n : ℕ) (p : MvPolynomial (Fin n) R) :
    finLastEquiv R n
      ((MvPolynomial.rename (PolynomialLocalRing.lowerVariableEmbedding n) p :
        MvPolynomial (Fin (n + 1)) R) : MvPowerSeries (Fin (n + 1)) R) =
      PowerSeries.C (p : MvPowerSeries (Fin n) R) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [MvPolynomial.rename_C, MvPolynomial.coe_C, MvPolynomial.coe_C, finLastEquiv_C]
  | add p q hp hq =>
      simp only [map_add, MvPolynomial.coe_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.rename_X, MvPolynomial.coe_mul,
        MvPolynomial.coe_X, hp, finLastEquiv_X_lowerVariableEmbedding]

end MvPowerSeries
