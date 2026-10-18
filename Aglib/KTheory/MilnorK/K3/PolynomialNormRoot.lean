/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialNorm
public import Aglib.RingTheory.AdjoinRootNormRoot

/-!
# The actual polynomial Milnor norm on a root and a constant

The actual residues of `{p,X,b}` at the two finite places `p` and `X`, and
its actual infinity residue, identify the polynomial-presentation Milnor K₂
norm of `{root,b}` with `{Algebra.norm(root),b}`. The sign is the signed
constant coefficient of the original monic polynomial. No general projection
formula, presentation independence, or extension-tower identity is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.PolynomialNorm

open Polynomial PolynomialResidue MilnorK.K2

variable {k : Type*} [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- The actual monic finite place defined by the variable. -/
abbrev variablePlace (k : Type*) [Field k] : MonicIrreducible k :=
  ⟨X, monic_X, irreducible_X⟩

/-- Nonzero constant coefficient excludes the variable place. -/
theorem ne_variablePlace (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) :
    p ≠ variablePlace k := by
  intro h
  apply hp0
  have hv := congrArg Subtype.val h
  rw [hv]
  exact coeff_X_zero

/-- The original root is nonzero precisely in the case considered here. -/
theorem not_dvd_variable (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) :
    ¬ p.val ∣ X :=
  not_dvd_of_ne (variablePlace k) p (Ne.symm (ne_variablePlace p hp0))

/-- The primitive polynomial root as its literal nonzero quotient unit. -/
def rootUnit (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) :
    (AdjoinRoot p.val)ˣ := quotientUnit p.val X (not_dvd_variable p hp0)

@[simp] theorem rootUnit_coe (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) :
    (rootUnit p hp0 : AdjoinRoot p.val) = AdjoinRoot.root p.val := rfl

/-- The nonzero constant coefficient, regarded as a base-field unit. -/
def constantCoeffUnit (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) : kˣ :=
  Units.mk0 (p.val.coeff 0) hp0

/-- A polynomial quotient unit at `X` is literally its constant coefficient. -/
theorem quotientUnit_variable (q : k[X]) (hq0 : q.coeff 0 ≠ 0) :
    quotientUnit (variablePlace k).val q (by simpa only [variablePlace, X_dvd_iff] using hq0) =
      Units.map (algebraMap k (AdjoinRoot (variablePlace k).val)).toMonoidHom
        (Units.mk0 (q.coeff 0) hq0) := by
  apply Units.ext
  apply (InfinityResidue.rootXEquiv k).injective
  change InfinityResidue.rootXEquiv k (AdjoinRoot.mk X q) =
    InfinityResidue.rootXEquiv k (algebraMap k (AdjoinRoot X) (q.coeff 0))
  rw [InfinityResidue.rootXEquiv_mk, (InfinityResidue.rootXEquiv k).commutes]
  exact (coeff_zero_eq_eval_zero q).symm

/-- The only actual finite residues of the symbol `{p,X,b}` are the normalized
root symbol at `p` and the negative constant-coefficient symbol at `X`. -/
theorem totalResidue_polynomial_variable_constant [DecidableEq (MonicIrreducible k)]
    (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) (b : kˣ) :
    totalResidue (symbol3 (polynomialUnit p.val p.property.2.ne_zero)
      (InfinityResidue.variableUnit k) (InfinityResidue.constantUnit k b)) =
      DFinsupp.single p (symbol (rootUnit p hp0)
        (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) -
      DFinsupp.single (variablePlace k)
        (MilnorK.K2.map (algebraMap k (AdjoinRoot (variablePlace k).val))
          (symbol (constantCoeffUnit p hp0) b)) := by
  classical
  apply DFinsupp.ext
  intro q
  rw [totalResidue_apply, DFinsupp.sub_apply,
    ← InfinityResidue.polynomialUnit_constant k b]
  by_cases hqp : q = p
  · subst q
    rw [DFinsupp.single_eq_same,
      DFinsupp.single_eq_of_ne (ne_variablePlace p hp0), sub_zero]
    change residueAt p.val (symbol3 (polynomialUnit p.val _)
      (polynomialUnit X X_ne_zero) (polynomialUnit (C (b : k)) _)) = _
    rw [residueAt_polynomial_units _ _ _ _ _
      (not_dvd_variable p hp0) (not_dvd_constant p b), quotientUnit_constant]
    rfl
  · rw [DFinsupp.single_eq_of_ne hqp]
    by_cases hqX : q = variablePlace k
    · subst q
      rw [DFinsupp.single_eq_same, zero_sub]
      change residueAt (variablePlace k).val (symbol3 (polynomialUnit p.val _)
        (polynomialUnit (variablePlace k).val X_ne_zero) (polynomialUnit (C (b : k)) _)) = _
      rw [symbol3_skew_left, map_neg,
        residueAt_polynomial_units _ _ _ _ _
          (by simpa only [variablePlace, X_dvd_iff] using hp0)
          (not_dvd_constant (variablePlace k) b),
        quotientUnit_variable p.val hp0, quotientUnit_constant, MilnorK.K2.map_symbol]
      rfl
    · rw [DFinsupp.single_eq_of_ne hqX, sub_zero]
      exact residueAt_polynomial_units_zero q.val _ X _ _ X_ne_zero _
        (not_dvd_of_ne p q (Ne.symm hqp))
        (not_dvd_of_ne (variablePlace k) q (Ne.symm hqX)) (not_dvd_constant q b)

private theorem symbol3_pow_first {K : Type*} [Field K] (a b c : Kˣ) (n : ℕ) :
    symbol3 (a ^ n) b c = n • symbol3 a b c := by
  have h := congrArg (symbol3FixedLast c) (symbol_pow_left a b n)
  simpa only [symbol3FixedLast_symbol, map_nsmul] using h

/-- The reversal of a monic polynomial reduces to the unit `1` at `X`. -/
theorem quotientUnit_reverse_variable (p : k[X]) (hp : p.Monic) :
    quotientUnit (variablePlace k).val p.reverse (InfinityResidue.not_dvd_reverse k p hp.ne_zero) =
      1 := by
  apply Units.ext
  apply (InfinityResidue.rootXEquiv k).injective
  change InfinityResidue.rootXEquiv k (AdjoinRoot.mk X p.reverse) =
    InfinityResidue.rootXEquiv k 1
  rw [InfinityResidue.rootXEquiv_mk, map_one, ← coeff_zero_eq_eval_zero,
    coeff_zero_reverse, hp.leadingCoeff]

/-- The actual infinity residue of `{p,X,b}` retains the full degree sign term. -/
theorem residue_polynomial_variable_constant (p : k[X]) (hp : p.Monic) (b : kˣ) :
    InfinityResidue.residue k (symbol3 (polynomialUnit p hp.ne_zero)
      (InfinityResidue.variableUnit k) (InfinityResidue.constantUnit k b)) =
      p.natDegree • symbol (-1) b := by
  have hreverse :
      residueAt (X : k[X]) (symbol3
        (polynomialUnit p.reverse (reverse_eq_zero.not.mpr hp.ne_zero))
        (InfinityResidue.variableUnit k) (InfinityResidue.constantUnit k b)) = 0 := by
    rw [symbol3_skew_left, map_neg, ← InfinityResidue.polynomialUnit_constant k b]
    change -residueAt (variablePlace k).val
      (symbol3 (polynomialUnit (variablePlace k).val X_ne_zero)
      (polynomialUnit p.reverse _) (polynomialUnit (C (b : k)) _)) = 0
    rw [residueAt_polynomial_units _ _ _ _ _
      (InfinityResidue.not_dvd_reverse k p hp.ne_zero) (not_dvd_constant (variablePlace k) b),
      quotientUnit_reverse_variable p hp, symbol_one_left, neg_zero]
  have hX : MilnorK.K2.map (InfinityResidue.rootXEquiv k).toRingHom
      (residueAt (X : k[X]) (symbol3 (InfinityResidue.variableUnit k)
        (InfinityResidue.constantUnit k (-1)) (InfinityResidue.constantUnit k b))) =
      symbol (-1) b := by
    rw [← InfinityResidue.polynomialUnit_constant k (-1),
      ← InfinityResidue.polynomialUnit_constant k b]
    change MilnorK.K2.map (InfinityResidue.rootXEquiv k).toRingHom
      (residueAt (X : k[X]) (symbol3 (polynomialUnit X X_ne_zero) _ _)) = _
    rw [residueAt_polynomial_units _ _ _ _ _
      (InfinityResidue.not_dvd_constant k (-1)) (InfinityResidue.not_dvd_constant k b),
      MilnorK.K2.map_symbol, InfinityResidue.rootXEquiv_quotientUnit_constant,
      InfinityResidue.rootXEquiv_quotientUnit_constant]
  have hsign : InfinityResidue.constantUnit k (-1) = (-1 : (RatFunc k)ˣ) := by
    apply Units.ext
    simp only [InfinityResidue.constantUnit_coe, Units.val_neg, Units.val_one, map_neg, map_one]
  rw [InfinityResidue.residue, LinearMap.comp_apply, LinearMap.comp_apply, map_symbol3,
    InfinityResidue.inversion_polynomialUnit, InfinityResidue.inversion_variableUnit,
    InfinityResidue.inversion_constantUnit, symbol3_mul_left, symbol3_pow_first,
    symbol3_inv_left, symbol3_inv_middle, neg_neg, symbol3_inv_middle,
    map_add, map_nsmul, map_neg, hreverse, neg_zero, add_zero,
    symbol3_self_left, ← hsign, map_nsmul, hX]

/-- The polynomial norm at `X` retracts the actual constant-field K₂ map. -/
theorem polynomialNorm_variable_map_constants (x : MilnorK.K2.Group k) :
    polynomialNorm (variablePlace k)
      (MilnorK.K2.map (algebraMap k (AdjoinRoot (variablePlace k).val)) x) = x := by
  simpa only [variablePlace, natDegree_X, Nat.cast_one, one_smul] using
    polynomialNorm_map_constants (variablePlace k) x

/-- The actual root-symbol norm is the signed constant-coefficient symbol. -/
theorem polynomialNorm_root_constant_coefficient
    (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) (b : kˣ) :
    polynomialNorm p (symbol (rootUnit p hp0)
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      symbol ((-1) ^ p.val.natDegree * constantCoeffUnit p hp0) b := by
  classical
  have h := totalNorm_totalResidue
    (symbol3 (polynomialUnit p.val p.property.2.ne_zero)
      (InfinityResidue.variableUnit k) (InfinityResidue.constantUnit k b))
  rw [totalResidue_polynomial_variable_constant p hp0 b, map_sub,
    totalNorm_single, totalNorm_single, polynomialNorm_variable_map_constants,
    residue_polynomial_variable_constant p.val p.property.1 b] at h
  have hsign : -symbol (-1 : kˣ) b = symbol (-1) b := by
    simpa only [inv_neg, inv_one] using (symbol_inv_left (-1 : kˣ) b).symm
  rw [symbol_mul_left, symbol_pow_left]
  rw [← neg_nsmul, hsign] at h
  exact sub_eq_iff_eq_add.mp h

/-- The ordinary determinant norm of the actual root unit is the signed
constant coefficient unit. -/
theorem norm_rootUnit (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) :
    Units.map (Algebra.norm k) (rootUnit p hp0) =
      (-1) ^ p.val.natDegree * constantCoeffUnit p hp0 := by
  apply Units.ext
  change Algebra.norm k (AdjoinRoot.root p.val) =
    (-1) ^ p.val.natDegree * p.val.coeff 0
  exact AdjoinRoot.norm_root p.val p.property.1

/-- On the primitive root paired with any base-field unit, the constructed
polynomial Milnor norm agrees with the ordinary determinant norm on units. -/
theorem polynomialNorm_root_constant
    (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) (b : kˣ) :
    polynomialNorm p (symbol (rootUnit p hp0)
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      symbol (Units.map (Algebra.norm k) (rootUnit p hp0)) b := by
  rw [norm_rootUnit, polynomialNorm_root_constant_coefficient]

end MilnorK.K3.PolynomialNorm
