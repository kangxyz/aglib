/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalRing
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# The actual map from a polynomial local ring to formal power series

The original polynomial map is native evaluation at the formal variables, with
coefficients mapped into the coefficient ring's completion. Denominators outside
the origin ideal become units by the constant-coefficient criterion. The resulting
native localization lift is proved local, rather than assuming a formal point.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace PolynomialLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Formal series over the actual coefficient completion. -/
abbrev FormalSeries (n : ℕ) :=
  MvPowerSeries (Fin n) (AdicCompletion (maximalIdeal R) R)

/-- The original polynomial map evaluates variables at the actual formal variables. -/
def polynomialToFormalSeries (n : ℕ) : MvPolynomial (Fin n) R →ₐ[R] FormalSeries R n :=
  MvPolynomial.aeval (fun i => (MvPowerSeries.X i : FormalSeries R n))

/-- Constant coefficients of polynomial evaluation are the completed original coefficients. -/
theorem constantCoeff_polynomialToFormalSeries (n : ℕ) (p : MvPolynomial (Fin n) R) :
    MvPowerSeries.constantCoeff (polynomialToFormalSeries R n p) =
      algebraMap R (AdicCompletion (maximalIdeal R) R) (MvPolynomial.constantCoeff p) := by
  have hX (i : Fin n) : polynomialToFormalSeries R n (MvPolynomial.X i) =
      MvPowerSeries.X i := MvPolynomial.aeval_X _ _
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [polynomialToFormalSeries, MvPolynomial.aeval_C, MvPolynomial.constantCoeff_C]
      rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i _ =>
      simp only [map_mul, hX, MvPowerSeries.constantCoeff_X, MvPolynomial.constantCoeff_X,
        mul_zero, map_zero]

variable [IsNoetherianRing R]

/-- Exactly the polynomials outside the origin ideal become formal units. -/
theorem isUnit_polynomialToFormalSeries_iff (n : ℕ) (p : MvPolynomial (Fin n) R) :
    IsUnit (polynomialToFormalSeries R n p) ↔ p ∉ originIdeal R n := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_polynomialToFormalSeries,
    isUnit_map_iff]
  change IsUnit (MvPolynomial.constantCoeff p) ↔ MvPolynomial.constantCoeff p ∉ maximalIdeal R
  exact IsLocalRing.notMem_maximalIdeal.symm

/-- The native localization lift into formal series over the coefficient completion. -/
def toFormalSeries (n : ℕ) : PolynomialLocalRing R n →ₐ[R] FormalSeries R n :=
  IsLocalization.liftAlgHom (S := PolynomialLocalRing R n)
    (f := polynomialToFormalSeries R n)
    (fun s : (originIdeal R n).primeCompl =>
      (isUnit_polynomialToFormalSeries_iff R n s).mpr s.property)

/-- The formal map restricts to the original polynomial evaluation. -/
theorem toFormalSeries_algebraMap (n : ℕ) (p : MvPolynomial (Fin n) R) :
    toFormalSeries R n (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) p) =
      polynomialToFormalSeries R n p := by
  exact IsLocalization.lift_eq (S := PolynomialLocalRing R n)
    (g := (polynomialToFormalSeries R n).toRingHom)
    (fun s : (originIdeal R n).primeCompl =>
      (isUnit_polynomialToFormalSeries_iff R n s).mpr s.property) p

instance toFormalSeries_isLocalHom (n : ℕ) : IsLocalHom (toFormalSeries R n).toRingHom := by
  constructor
  intro x hx
  obtain ⟨p, s, rfl⟩ := IsLocalization.exists_mk'_eq (originIdeal R n).primeCompl x
  apply (IsLocalization.AtPrime.isUnit_mk'_iff
    (PolynomialLocalRing R n) (originIdeal R n) p s).mpr
  have hs : IsUnit (polynomialToFormalSeries R n s) :=
    (isUnit_polynomialToFormalSeries_iff R n s).mpr s.property
  have he := congrArg (toFormalSeries R n) (IsLocalization.mk'_spec (PolynomialLocalRing R n) p s)
  rw [map_mul, toFormalSeries_algebraMap, toFormalSeries_algebraMap] at he
  have hp : IsUnit (polynomialToFormalSeries R n p) := by
    rw [← he]
    exact hx.mul hs
  exact (isUnit_polynomialToFormalSeries_iff R n p).mp hp

end PolynomialLocalRing
