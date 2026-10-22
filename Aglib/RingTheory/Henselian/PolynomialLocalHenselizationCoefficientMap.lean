/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationFormal

/-!
# The original polynomial coefficient map in formal evaluation

The actual henselization formal map restricts to the native polynomial
coefficient action. The source map is written as its original localization
and henselization composite, without choosing an auxiliary algebra action.
-/

@[expose] public noncomputable section

namespace PolynomialLocalHenselization

variable (k : Type*) [CommRing k] [IsLocalRing k] [IsNoetherianRing k]

/-- The original henselized formal map restricts to the native polynomial
coefficient map, including its completed coefficient action. -/
theorem toFormalSeries_comp_polynomial_algebraMap (n : ℕ) :
    (toFormalSeries k n).toRingHom.comp
      ((algebraMap (PolynomialLocalRing k n) (PolynomialLocalHenselization k n)).comp
        (algebraMap (MvPolynomial (Fin n) k) (PolynomialLocalRing k n))) =
      algebraMap (MvPolynomial (Fin n) k) (PolynomialLocalRing.FormalSeries k n) := by
  let P := MvPolynomial (Fin n) k
  let L := PolynomialLocalRing k n
  let H := PolynomialLocalHenselization k n
  let C := PolynomialLocalRing.FormalSeries k n
  have hp : PolynomialLocalRing.polynomialToFormalSeries k n =
      MvPolynomial.coeToMvPowerSeries.algHom
        (AdicCompletion (IsLocalRing.maximalIdeal k) k) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [PolynomialLocalRing.polynomialToFormalSeries, MvPolynomial.aeval_X,
      MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.coe_X, MvPowerSeries.map_X]
  apply RingHom.ext
  intro p
  change toFormalSeries k n (algebraMap L H (algebraMap P L p)) = algebraMap P C p
  have h := AlgHom.congr_fun (toFormalSeries_comp_of k n) (algebraMap P L p)
  change toFormalSeries k n (algebraMap L H (algebraMap P L p)) =
    PolynomialLocalRing.toFormalSeries k n (algebraMap P L p) at h
  rw [h, PolynomialLocalRing.toFormalSeries_algebraMap]
  exact AlgHom.congr_fun hp p

end PolynomialLocalHenselization
