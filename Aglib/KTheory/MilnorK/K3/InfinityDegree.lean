/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.InfinityResidue
public import Aglib.FieldTheory.RatFuncReverse

/-!
# Actual infinity residue of a polynomial and two constants

For every nonzero polynomial over any field, the actual infinity residue of
`{p,a,b}` is `−natDegree(p) • {a,b}` in the original Milnor K₂ group. Inversion
factors `p` into the inverse variable to its degree and its reverse. The latter
has nonzero constant coefficient and hence zero actual finite residue at `X`.
No norm, reciprocity, or degree formula is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.InfinityResidue

open Polynomial MilnorK.K2 PolynomialResidue

variable (k : Type*) [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- The reverse of a nonzero polynomial is prime to the finite place `X`. -/
theorem not_dvd_reverse (p : k[X]) (hp : p ≠ 0) :
    ¬ (X : k[X]) ∣ p.reverse := by
  simpa only [X_dvd_iff, coeff_zero_reverse] using (leadingCoeff_ne_zero.mpr hp)

/-- Actual inversion factors the polynomial unit into an inverse-variable power
and the literal reversed-polynomial unit. -/
theorem inversion_polynomialUnit (p : k[X]) (hp : p ≠ 0) :
    Units.map (RatFunc.inversion k).toRingHom.toMonoidHom (polynomialUnit p hp) =
      (variableUnit k)⁻¹ ^ p.natDegree *
        polynomialUnit p.reverse (reverse_eq_zero.not.mpr hp) := by
  apply Units.ext
  change RatFunc.inversion k (algebraMap k[X] (RatFunc k) p) =
    (RatFunc.X⁻¹ : RatFunc k) ^ p.natDegree * algebraMap k[X] (RatFunc k) p.reverse
  exact RatFunc.inversion_algebraMap_reverse k p

/-- The reversed polynomial contributes no actual finite residue at `X`. -/
theorem residueAt_reverse_constants (p : k[X]) (hp : p ≠ 0) (a b : kˣ) :
    residueAt (X : k[X])
      (symbol3 (polynomialUnit p.reverse (reverse_eq_zero.not.mpr hp))
        (constantUnit k a) (constantUnit k b)) = 0 := by
  rw [← polynomialUnit_constant k a, ← polynomialUnit_constant k b]
  exact residueAt_polynomial_units_zero X p.reverse (C (a : k)) (C (b : k))
    (reverse_eq_zero.not.mpr hp) (C_ne_zero.mpr a.ne_zero) (C_ne_zero.mpr b.ne_zero)
    (not_dvd_reverse k p hp) (not_dvd_constant k a) (not_dvd_constant k b)

private theorem symbol3_pow_first {K : Type*} [Field K] (a b c : Kˣ) (n : ℕ) :
    symbol3 (a ^ n) b c = n • symbol3 a b c := by
  have h := congrArg (symbol3FixedLast c) (symbol_pow_left a b n)
  simpa only [symbol3FixedLast_symbol, map_nsmul] using h

/-- The degree formula for the constructed infinity residue, in the original
Milnor K₂ quotient, with its negative sign and arbitrary nonzero polynomial. -/
theorem residue_polynomial_constants (p : k[X]) (hp : p ≠ 0) (a b : kˣ) :
    residue k (symbol3 (polynomialUnit p hp) (constantUnit k a) (constantUnit k b)) =
      -(p.natDegree : ℤ) • symbol a b := by
  have hX := residue_inv_variable k a b
  rw [residue, LinearMap.comp_apply, LinearMap.comp_apply, map_symbol3,
    map_inv, inversion_variableUnit, inv_inv, inversion_constantUnit,
    inversion_constantUnit] at hX
  rw [residue, LinearMap.comp_apply, LinearMap.comp_apply, map_symbol3,
    inversion_polynomialUnit, inversion_constantUnit, inversion_constantUnit,
    symbol3_mul_left, symbol3_pow_first, symbol3_inv_left, map_add, map_nsmul,
    map_neg, residueAt_reverse_constants k p hp a b, add_zero, map_nsmul, map_neg, hX]
  simp only [neg_smul, natCast_zsmul, smul_neg]

end MilnorK.K3.InfinityResidue
