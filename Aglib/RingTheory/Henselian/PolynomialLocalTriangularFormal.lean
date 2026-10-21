/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalTriangular
public import Aglib.RingTheory.Henselian.PolynomialLocalFormal
public import Aglib.RingTheory.MvPowerSeries.Triangular

/-!
# Original-map compatibility of local and formal triangular coordinates

The same triangular polynomial substitution induces the native local-ring
coordinate equivalence and the already constructed formal substitution
equivalence. Their square is checked on actual polynomial generators and then
on the localization. The inverse square follows from the genuine inverse laws.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace PolynomialLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
variable (p : Fin n) (e : Fin n → ℕ) (he : ∀ i, i ≠ p → 0 < e i)

/-- The original local triangular map intertwines the original formal evaluations. -/
theorem toFormalSeries_comp_triangularAlgEquiv :
    (toFormalSeries R n).comp (triangularAlgEquiv R n p e he).toAlgHom =
      ((MvPowerSeries.triangularAlgEquiv
        (R := AdicCompletion (maximalIdeal R) R) p e he).restrictScalars R).toAlgHom.comp
          (toFormalSeries R n) := by
  apply IsLocalization.algHom_ext (originIdeal R n).primeCompl
  apply MvPolynomial.algHom_ext
  intro i
  change toFormalSeries R n (triangularAlgEquiv R n p e he
    (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) (MvPolynomial.X i))) =
    MvPowerSeries.triangularAlgEquiv (R := AdicCompletion (maximalIdeal R) R) p e he
      (toFormalSeries R n (algebraMap (MvPolynomial (Fin n) R)
        (PolynomialLocalRing R n) (MvPolynomial.X i)))
  rw [triangularAlgEquiv_algebraMap, toFormalSeries_algebraMap, toFormalSeries_algebraMap,
    MvPolynomial.triangularAlgEquiv_X]
  by_cases hi : i = p
  · simp only [hi, ite_true, polynomialToFormalSeries, MvPolynomial.aeval_X,
      MvPowerSeries.triangularAlgEquiv_X]
  · simp only [hi, ite_false, map_add, map_pow, polynomialToFormalSeries,
      MvPolynomial.aeval_X, MvPowerSeries.triangularAlgEquiv_X]

/-- The inverse local and formal coordinate changes also commute literally. -/
theorem toFormalSeries_triangularAlgEquiv_symm (x : PolynomialLocalRing R n) :
    toFormalSeries R n ((triangularAlgEquiv R n p e he).symm x) =
      (MvPowerSeries.triangularAlgEquiv
        (R := AdicCompletion (maximalIdeal R) R) p e he).symm (toFormalSeries R n x) := by
  let a := triangularAlgEquiv R n p e he
  let b := MvPowerSeries.triangularAlgEquiv
    (R := AdicCompletion (maximalIdeal R) R) p e he
  apply b.injective
  have h := AlgHom.congr_fun (toFormalSeries_comp_triangularAlgEquiv R n p e he) (a.symm x)
  change toFormalSeries R n (a (a.symm x)) = b (toFormalSeries R n (a.symm x)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  change b (toFormalSeries R n (a.symm x)) = b (b.symm (toFormalSeries R n x))
  rw [AlgEquiv.apply_symm_apply]
  exact h.symm

end PolynomialLocalRing
