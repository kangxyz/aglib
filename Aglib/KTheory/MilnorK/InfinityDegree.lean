/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.InfinityResidue
public import Aglib.FieldTheory.RatFuncReverse

/-!
# The all-degree polynomial degree formula at infinity

For a nonzero polynomial `p` and any tuple of constants, the actual last-slot
infinity residue is `−natDegree(p)` times the symbol of constants. The proof
uses the actual inversion factorization of `p` into an inverse-variable power
and its reverse, and actual all-unit vanishing for the reversed polynomial.
The proof includes the empty tuple and makes no norm or reciprocity assumption.
-/

@[expose] public noncomputable section

namespace MilnorK.InfinityResidue

open Polynomial PolynomialResidue

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

/-- The reversed polynomial and all constants are actual local units at `X`. -/
theorem residueAt_constants_reverse (n : ℕ) (p : k[X]) (hp : p ≠ 0)
    (a : SymbolTuple k n) :
    residueAt (X : k[X]) n
      (symbol (Fin.snoc (constantUnit k ∘ a)
        (polynomialUnit p.reverse (reverse_eq_zero.not.mpr hp)))) = 0 := by
  let q : Fin (n + 1) → k[X] := Fin.snoc (fun i => C (a i : k)) p.reverse
  have hq : ∀ i, q i ≠ 0 := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa only [q, Fin.snoc_last] using reverse_eq_zero.not.mpr hp
    | cast i => simpa only [q, Fin.snoc_castSucc] using C_ne_zero.mpr (a i).ne_zero
  have hqp : ∀ i, ¬ (X : k[X]) ∣ q i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa only [q, Fin.snoc_last] using not_dvd_reverse k p hp
    | cast i => simpa only [q, Fin.snoc_castSucc] using not_dvd_constant k (a i)
  have ht : (fun i => polynomialUnit (q i) (hq i)) =
      Fin.snoc (constantUnit k ∘ a) (polynomialUnit p.reverse (reverse_eq_zero.not.mpr hp)) := by
    funext i
    cases i using Fin.lastCases with
    | last => simp only [q, Fin.snoc_last]
    | cast i =>
        simpa only [q, Fin.snoc_castSucc, Function.comp_apply] using
          polynomialUnit_constant k (a i)
  rw [← ht]
  exact residueAt_polynomial_units_zero X n q hq hqp

private theorem symbol_snoc_mul {F : Type*} [Field F] {n : ℕ}
    (a : SymbolTuple F n) (b c : Fˣ) :
    symbol (Fin.snoc a (b * c)) = symbol (Fin.snoc a b) + symbol (Fin.snoc a c) := by
  simpa only [productUnit_symbol, toMul_add, toMul_ofMul] using
    map_add (productUnit n (symbol a)) (Additive.ofMul b) (Additive.ofMul c)

private theorem symbol_snoc_inv {F : Type*} [Field F] {n : ℕ}
    (a : SymbolTuple F n) (b : Fˣ) :
    symbol (Fin.snoc a b⁻¹) = -symbol (Fin.snoc a b) := by
  simpa only [productUnit_symbol, toMul_neg, toMul_ofMul] using
    map_neg (productUnit n (symbol a)) (Additive.ofMul b)

private theorem symbol_snoc_pow {F : Type*} [Field F] {n : ℕ}
    (a : SymbolTuple F n) (b : Fˣ) (m : ℕ) :
    symbol (Fin.snoc a (b ^ m)) = m • symbol (Fin.snoc a b) := by
  simpa only [productUnit_symbol, toMul_nsmul, toMul_ofMul] using
    map_nsmul (productUnit n (symbol a)) m (Additive.ofMul b)

/-- A polynomial in the last slot has actual infinity residue with coefficient minus its degree. -/
theorem residue_polynomial_constants (n : ℕ) (p : k[X]) (hp : p ≠ 0)
    (a : SymbolTuple k n) :
    residue k n (symbol (Fin.snoc (constantUnit k ∘ a) (polynomialUnit p hp))) =
      -(p.natDegree : ℤ) • symbol a := by
  have hX := residue_inv_variable k n a
  rw [residue, LinearMap.comp_apply, LinearMap.comp_apply, MilnorK.map_symbol,
    Fin.comp_snoc, map_inv, inversion_variableUnit, inv_inv, inversion_constant_tuple] at hX
  rw [residue, LinearMap.comp_apply, LinearMap.comp_apply, MilnorK.map_symbol,
    Fin.comp_snoc, inversion_polynomialUnit, inversion_constant_tuple,
    symbol_snoc_mul, symbol_snoc_pow, symbol_snoc_inv, map_add, map_nsmul,
    map_neg, residueAt_constants_reverse k n p hp a, add_zero, map_nsmul, map_neg, hX]
  simp only [neg_smul, natCast_zsmul, smul_neg]

end MilnorK.InfinityResidue
