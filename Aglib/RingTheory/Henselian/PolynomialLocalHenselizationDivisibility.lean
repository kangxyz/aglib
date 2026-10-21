/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationPrecision
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Descent of square-divisibility precision to the actual higher henselization

The exact polynomial evaluation square transfers formal information about the
actual source quotients to the higher henselization. Localness reflects the
unit quotient, and the proved finite-quotient comparison reflects ideal-power
precision. Thus the error belongs to the minor squared times the source ideal,
not merely to the corresponding formal ideal.
-/

@[expose] public section

namespace PolynomialLocalHenselization

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A formally small source polynomial evaluates to a genuinely small element
of the actual higher henselization. -/
theorem polynomialEvaluation_mem_maximalIdeal_pow_of_formal
    (n c : ℕ) (Q : Polynomial (PolynomialLocalHenselization R n))
    (hQ : (Q.map (toFormalSeries R n).toRingHom :
      PowerSeries (PolynomialLocalRing.FormalSeries R n)) ∈
        IsLocalRing.maximalIdeal (PowerSeries (PolynomialLocalRing.FormalSeries R n)) ^ c) :
    polynomialEvaluation R n Q ∈
      IsLocalRing.maximalIdeal (PolynomialLocalHenselization R (n + 1)) ^ c := by
  apply (iteratedFormalMap_mem_maximalIdeal_pow_iff R n c _).mp
  have hs := RingHom.congr_fun (iteratedFormalMap_comp_polynomialEvaluation R n) Q
  change iteratedFormalMap R n (polynomialEvaluation R n Q) =
    (Q.map (toFormalSeries R n).toRingHom :
      PowerSeries (PolynomialLocalRing.FormalSeries R n)) at hs
  rw [hs]
  exact hQ

/-- A formally unit source polynomial evaluates to a unit in the actual higher
henselization through the concrete local formal map. -/
theorem isUnit_polynomialEvaluation_of_formal
    (n : ℕ) (q : Polynomial (PolynomialLocalHenselization R n))
    (hq : IsUnit (q.map (toFormalSeries R n).toRingHom :
      PowerSeries (PolynomialLocalRing.FormalSeries R n))) :
    IsUnit (polynomialEvaluation R n q) := by
  apply IsLocalHom.map_nonunit
    (R := PolynomialLocalHenselization R (n + 1))
    (S := PowerSeries (PolynomialLocalRing.FormalSeries R n))
    (f := (iteratedFormalMap R n).toRingHom)
  have hs := RingHom.congr_fun (iteratedFormalMap_comp_polynomialEvaluation R n) q
  change iteratedFormalMap R n (polynomialEvaluation R n q) =
    (q.map (toFormalSeries R n).toRingHom :
      PowerSeries (PolynomialLocalRing.FormalSeries R n)) at hs
  change IsUnit (iteratedFormalMap R n (polynomialEvaluation R n q))
  rw [hs]
  exact hq

/-- Source polynomial factorization and the actual formal quotient estimates
supply the square-times-source-ideal hypothesis for determinant correction. -/
theorem polynomialEvaluation_mem_minor_sq_mul_of_formal_quotients
    (n c : ℕ) (P q Q G F : Polynomial (PolynomialLocalHenselization R n))
    (hg : G = P * q) (hf : F = P ^ 2 * Q)
    (hq : IsUnit (q.map (toFormalSeries R n).toRingHom :
      PowerSeries (PolynomialLocalRing.FormalSeries R n)))
    (hQ : (Q.map (toFormalSeries R n).toRingHom :
      PowerSeries (PolynomialLocalRing.FormalSeries R n)) ∈
        IsLocalRing.maximalIdeal (PowerSeries (PolynomialLocalRing.FormalSeries R n)) ^ c) :
    polynomialEvaluation R n F ∈
      Ideal.span {(polynomialEvaluation R n G) ^ 2} *
        IsLocalRing.maximalIdeal (PolynomialLocalHenselization R (n + 1)) ^ c := by
  have hqunit := isUnit_polynomialEvaluation_of_formal R n q hq
  have hQmem := polynomialEvaluation_mem_maximalIdeal_pow_of_formal R n c Q hQ
  rw [hg, map_mul, mul_pow, Ideal.span_singleton_mul_right_unit (hqunit.pow 2)]
  apply Ideal.mem_span_singleton_mul.mpr
  refine ⟨_, hQmem, ?_⟩
  rw [hf, map_mul, map_pow]

end PolynomialLocalHenselization
