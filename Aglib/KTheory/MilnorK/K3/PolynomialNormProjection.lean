/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialNormRoot
public import Aglib.RingTheory.AdjoinRootNormResultant

/-!
# The mixed projection formula for the actual polynomial Milnor norm

The two-place residue identity for `{p,q,b}` retains the degree-product sign
at infinity. Factorization of reduced polynomial representatives and induction
on the actual polynomial degree give the mixed projection formula.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.PolynomialNorm

open Polynomial PolynomialResidue MilnorK.K2

variable {k : Type*} [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- The actual finite residues of two distinct monic irreducibles and a constant. -/
theorem totalResidue_polynomials_constant [DecidableEq (MonicIrreducible k)]
    (p q : MonicIrreducible k) (hpq : p ≠ q) (b : kˣ) :
    totalResidue (symbol3 (polynomialUnit p.val p.property.2.ne_zero)
      (polynomialUnit q.val q.property.2.ne_zero) (InfinityResidue.constantUnit k b)) =
      DFinsupp.single p (symbol (quotientUnit p.val q.val (not_dvd_of_ne q p hpq.symm))
        (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) -
      DFinsupp.single q (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq))
        (Units.map (algebraMap k (AdjoinRoot q.val)).toMonoidHom b)) := by
  classical
  apply DFinsupp.ext
  intro r
  rw [totalResidue_apply, DFinsupp.sub_apply,
    ← InfinityResidue.polynomialUnit_constant k b]
  by_cases hrp : r = p
  · subst r
    rw [DFinsupp.single_eq_same, DFinsupp.single_eq_of_ne hpq, sub_zero,
      residueAt_polynomial_units _ _ _ _ _ (not_dvd_of_ne q p hpq.symm)
        (not_dvd_constant p b), quotientUnit_constant]
  · rw [DFinsupp.single_eq_of_ne hrp]
    by_cases hrq : r = q
    · subst r
      rw [DFinsupp.single_eq_same, zero_sub, symbol3_skew_left, map_neg,
        residueAt_polynomial_units _ _ _ _ _ (not_dvd_of_ne p q hpq)
          (not_dvd_constant q b), quotientUnit_constant]
    · rw [DFinsupp.single_eq_of_ne hrq, sub_zero]
      exact residueAt_polynomial_units_zero r.val _ _ _ _ _ _
        (not_dvd_of_ne p r (Ne.symm hrp)) (not_dvd_of_ne q r (Ne.symm hrq))
        (not_dvd_constant r b)

private theorem symbol3_pow_first {K : Type*} [Field K] (a b c : Kˣ) (n : ℕ) :
    symbol3 (a ^ n) b c = n • symbol3 a b c := by
  have h := congrArg (symbol3FixedLast c) (symbol_pow_left a b n)
  simpa only [symbol3FixedLast_symbol, map_nsmul] using h

private theorem symbol3_pow_middle {K : Type*} [Field K] (a b c : Kˣ) (n : ℕ) :
    symbol3 a (b ^ n) c = n • symbol3 a b c := by
  have h := congrArg (symbol3FixedLast c) (symbol_pow_right a b n)
  simpa only [symbol3FixedLast_symbol, map_nsmul] using h

private theorem residueAt_variable_reverse_constant (p : k[X]) (hp : p.Monic) (b : kˣ) :
    residueAt (X : k[X]) (symbol3 (InfinityResidue.variableUnit k)
      (polynomialUnit p.reverse (reverse_eq_zero.not.mpr hp.ne_zero))
      (InfinityResidue.constantUnit k b)) = 0 := by
  rw [← InfinityResidue.polynomialUnit_constant k b]
  change residueAt (variablePlace k).val
    (symbol3 (polynomialUnit (variablePlace k).val X_ne_zero)
      (polynomialUnit p.reverse _) (polynomialUnit (C (b : k)) _)) = 0
  rw [residueAt_polynomial_units _ _ _ _ _
    (InfinityResidue.not_dvd_reverse k p hp.ne_zero) (not_dvd_constant (variablePlace k) b),
    quotientUnit_reverse_variable p hp, symbol_one_left]

private theorem residueAt_reverse_variable_constant (p : k[X]) (hp : p.Monic) (b : kˣ) :
    residueAt (X : k[X]) (symbol3
      (polynomialUnit p.reverse (reverse_eq_zero.not.mpr hp.ne_zero))
      (InfinityResidue.variableUnit k) (InfinityResidue.constantUnit k b)) = 0 := by
  rw [symbol3_skew_left, map_neg, residueAt_variable_reverse_constant p hp b, neg_zero]

private theorem residueAt_reverses_constant (p q : k[X]) (hp : p.Monic) (hq : q.Monic)
    (b : kˣ) :
    residueAt (X : k[X]) (symbol3
      (polynomialUnit p.reverse (reverse_eq_zero.not.mpr hp.ne_zero))
      (polynomialUnit q.reverse (reverse_eq_zero.not.mpr hq.ne_zero))
      (InfinityResidue.constantUnit k b)) = 0 := by
  rw [← InfinityResidue.polynomialUnit_constant k b]
  exact residueAt_polynomial_units_zero X _ _ _ _ _ _
    (InfinityResidue.not_dvd_reverse k p hp.ne_zero)
    (InfinityResidue.not_dvd_reverse k q hq.ne_zero)
    (InfinityResidue.not_dvd_constant k b)

private theorem residueAt_variable_variable_constant (b : kˣ) :
    MilnorK.K2.map (InfinityResidue.rootXEquiv k).toRingHom
      (residueAt (X : k[X]) (symbol3 (InfinityResidue.variableUnit k)
        (InfinityResidue.variableUnit k) (InfinityResidue.constantUnit k b))) =
      symbol (-1) b := by
  have hsign : InfinityResidue.constantUnit k (-1) = (-1 : (RatFunc k)ˣ) := by
    apply Units.ext
    simp only [InfinityResidue.constantUnit_coe, Units.val_neg, Units.val_one, map_neg, map_one]
  rw [symbol3_self_left, ← hsign, ← InfinityResidue.polynomialUnit_constant k (-1),
    ← InfinityResidue.polynomialUnit_constant k b]
  change MilnorK.K2.map (InfinityResidue.rootXEquiv k).toRingHom
    (residueAt (X : k[X]) (symbol3 (polynomialUnit X X_ne_zero) _ _)) = _
  rw [residueAt_polynomial_units _ _ _ _ _
    (InfinityResidue.not_dvd_constant k (-1)) (InfinityResidue.not_dvd_constant k b),
    MilnorK.K2.map_symbol, InfinityResidue.rootXEquiv_quotientUnit_constant,
    InfinityResidue.rootXEquiv_quotientUnit_constant]

/-- The infinity residue of two monic polynomial entries is the full product-of-degrees sign. -/
theorem residue_polynomials_constant (p q : k[X]) (hp : p.Monic) (hq : q.Monic) (b : kˣ) :
    InfinityResidue.residue k (symbol3 (polynomialUnit p hp.ne_zero)
      (polynomialUnit q hq.ne_zero) (InfinityResidue.constantUnit k b)) =
      (p.natDegree * q.natDegree) • symbol (-1) b := by
  rw [InfinityResidue.residue, LinearMap.comp_apply, LinearMap.comp_apply, map_symbol3,
    InfinityResidue.inversion_polynomialUnit, InfinityResidue.inversion_polynomialUnit,
    InfinityResidue.inversion_constantUnit]
  simp only [symbol3_mul_left, symbol3_mul_middle, symbol3_pow_first, symbol3_pow_middle,
    symbol3_inv_left, symbol3_inv_middle, map_add, map_nsmul, map_neg,
    residueAt_variable_reverse_constant q hq b,
    residueAt_reverse_variable_constant p hp b,
    residueAt_reverses_constant p q hp hq b, neg_zero, nsmul_zero, add_zero,
    residueAt_variable_variable_constant b, mul_nsmul]
  simp only [smul_neg, neg_neg]

/-- The determinant norm on original constant units has the actual polynomial degree. -/
theorem norm_constantUnit (p : MonicIrreducible k) (a : kˣ) :
    Units.map (Algebra.norm k)
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom a) = a ^ p.val.natDegree := by
  apply Units.ext
  change Algebra.norm k (algebraMap k (AdjoinRoot p.val) (a : k)) = (a : k) ^ p.val.natDegree
  rw [Algebra.norm_algebraMap]
  congr 1
  exact finrank_quotient_span_eq_natDegree

/-- The mixed formula on constants follows from the already constructed degree identity. -/
theorem polynomialNorm_constant_constant (p : MonicIrreducible k) (a b : kˣ) :
    polynomialNorm p (symbol
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom a)
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      symbol (Units.map (Algebra.norm k)
        (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom a)) b := by
  rw [← MilnorK.K2.map_symbol, polynomialNorm_map_constant_symbol,
    norm_constantUnit, symbol_pow_left, natCast_zsmul]


/-- Actual two-place reciprocity, with the sign retained in the original K₂ group. -/
theorem polynomialNorm_polynomial_reciprocity (p q : MonicIrreducible k)
    (hpq : p ≠ q) (b : kˣ) :
    polynomialNorm p (symbol (quotientUnit p.val q.val (not_dvd_of_ne q p hpq.symm))
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      polynomialNorm q (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq))
        (Units.map (algebraMap k (AdjoinRoot q.val)).toMonoidHom b)) +
      (p.val.natDegree * q.val.natDegree) • symbol (-1) b := by
  classical
  have h := totalNorm_totalResidue
    (symbol3 (polynomialUnit p.val p.property.2.ne_zero)
      (polynomialUnit q.val q.property.2.ne_zero) (InfinityResidue.constantUnit k b))
  rw [totalResidue_polynomials_constant p q hpq b, map_sub, totalNorm_single,
    totalNorm_single, residue_polynomials_constant p.val q.val p.property.1 q.property.1 b] at h
  have hsign : -symbol (-1 : kˣ) b = symbol (-1) b := by
    simpa only [inv_neg, inv_one] using (symbol_inv_left (-1 : kˣ) b).symm
  rw [← neg_nsmul, hsign] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

private theorem quotientUnit_mul (p : MonicIrreducible k) (a b : k[X])
    (ha : ¬ p.val ∣ a) (hb : ¬ p.val ∣ b) (hab : ¬ p.val ∣ a * b) :
    quotientUnit p.val (a * b) hab = quotientUnit p.val a ha * quotientUnit p.val b hb := by
  apply Units.ext
  exact map_mul (AdjoinRoot.mk p.val) a b

private theorem quotientUnit_prod_property (p : MonicIrreducible k)
    (P : (AdjoinRoot p.val)ˣ → Prop) (hone : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b))
    (s : Multiset k[X]) (hs : ¬ p.val ∣ s.prod)
    (hP : ∀ a ∈ s, ∀ ha : ¬ p.val ∣ a, P (quotientUnit p.val a ha)) :
    P (quotientUnit p.val s.prod hs) := by
  induction s using Multiset.induction_on with
  | empty =>
    have hunit : quotientUnit p.val (0 : Multiset k[X]).prod hs = 1 := by
      apply Units.ext
      exact map_one (AdjoinRoot.mk p.val)
    rw [hunit]
    exact hone
  | cons a s ih =>
    simp only [Multiset.prod_cons] at hs ⊢
    have ha : ¬ p.val ∣ a := fun h => hs (dvd_mul_of_dvd_left h _)
    have hs' : ¬ p.val ∣ s.prod := fun h => hs (dvd_mul_of_dvd_right h _)
    rw [quotientUnit_mul p a s.prod ha hs' hs]
    exact hmul _ _ (hP a (Multiset.mem_cons_self a s) ha)
      (ih hs' (fun c hc => hP c (Multiset.mem_cons_of_mem hc)))

/-- Multiplicative predicates on residue-field units reduce to constants and
monic irreducibles smaller than the original defining polynomial. -/
private theorem reduced_factor_induction (p : MonicIrreducible k)
    (P : (AdjoinRoot p.val)ˣ → Prop) (hone : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b))
    (hconstant : ∀ c : kˣ, P (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom c))
    (hirreducible : ∀ (q : MonicIrreducible k) (hqdeg : q.val.natDegree < p.val.natDegree),
      P (quotientUnit p.val q.val
        (p.property.1.not_dvd_of_natDegree_lt q.property.2.ne_zero hqdeg)))
    (a : (AdjoinRoot p.val)ˣ) : P a := by
  classical
  let A := DegreeFiltration.reducedRepresentative p.val p.property.1 a
  have hA : A ≠ 0 := DegreeFiltration.reducedRepresentative_ne_zero p.val p.property.1 a
  have hAdeg : A.natDegree < p.val.natDegree :=
    DegreeFiltration.reducedRepresentative_natDegree_lt p.val p.property.1 a
  have hAp : ¬ p.val ∣ A := p.property.1.not_dvd_of_natDegree_lt hA hAdeg
  let s := UniqueFactorizationMonoid.normalizedFactors A
  have hfactor : C A.leadingCoeff * s.prod = A :=
    Polynomial.leadingCoeff_mul_prod_normalizedFactors A
  have hs : ¬ p.val ∣ s.prod := by
    intro h
    apply hAp
    rw [← hfactor]
    exact dvd_mul_of_dvd_right h _
  have hP : ∀ q ∈ s, ∀ hq : ¬ p.val ∣ q, P (quotientUnit p.val q hq) := by
    intro q hq hqp
    obtain ⟨hqi, hqm, hqdvd⟩ := (Polynomial.mem_normalizedFactors_iff hA).mp hq
    have hqdeg := (Polynomial.natDegree_le_of_dvd hqdvd hA).trans_lt hAdeg
    exact hirreducible ⟨q, hqm, hqi⟩ hqdeg
  let c : kˣ := Units.mk0 A.leadingCoeff (leadingCoeff_ne_zero.mpr hA)
  have hcp : ¬ p.val ∣ C A.leadingCoeff := not_dvd_constant p c
  have hc : P (quotientUnit p.val (C A.leadingCoeff) hcp) := by
    change P (quotientUnit p.val (C (c : k)) (not_dvd_constant p c))
    rw [quotientUnit_constant]
    exact hconstant c
  have hprod := quotientUnit_prod_property p P hone hmul s hs hP
  have ha : quotientUnit p.val A hAp = a :=
    DegreeFiltration.quotientUnit_reducedRepresentative p.val p.property.1 a
  have hunit : quotientUnit p.val A hAp =
      quotientUnit p.val (C A.leadingCoeff) hcp * quotientUnit p.val s.prod hs := by
    apply Units.ext
    change AdjoinRoot.mk p.val A = AdjoinRoot.mk p.val (C A.leadingCoeff) *
      AdjoinRoot.mk p.val s.prod
    rw [← map_mul, hfactor]
  rw [← ha, hunit]
  exact hmul _ _ hc hprod


/-- Ordinary determinant reciprocity for the literal nonzero quotient units. -/
theorem norm_quotientUnit_reciprocity [CharZero k] (p q : MonicIrreducible k)
    (hpq : p ≠ q) :
    Units.map (Algebra.norm k) (quotientUnit p.val q.val (not_dvd_of_ne q p hpq.symm)) =
      (-1) ^ (p.val.natDegree * q.val.natDegree) *
        Units.map (Algebra.norm k) (quotientUnit q.val p.val (not_dvd_of_ne p q hpq)) := by
  apply Units.ext
  exact AdjoinRoot.norm_mk_reciprocity p.val q.val p.property.1 q.property.1

/-- The actual polynomial Milnor norm on every mixed symbol agrees with the
ordinary determinant norm on its arbitrary residue-field unit. -/
theorem polynomialNorm_symbol_constant [CharZero k] (p : MonicIrreducible k)
    (a : (AdjoinRoot p.val)ˣ) (b : kˣ) :
    polynomialNorm p (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
      symbol (Units.map (Algebra.norm k) a) b := by
  suffices hmain : ∀ d : ℕ, ∀ p : MonicIrreducible k, p.val.natDegree = d →
      ∀ (a : (AdjoinRoot p.val)ˣ) (b : kˣ),
        polynomialNorm p
          (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
          symbol (Units.map (Algebra.norm k) a) b from
    hmain p.val.natDegree p rfl a b
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro p hpdeg a b
    apply reduced_factor_induction p
      (fun u => polynomialNorm p
        (symbol u (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b)) =
        symbol (Units.map (Algebra.norm k) u) b) ?_ ?_ ?_ ?_ a
    · simp only [symbol_one_left, map_zero, map_one]
    · intro u v hu hv
      rw [symbol_mul_left, map_add, map_mul, symbol_mul_left, hu, hv]
    · intro c
      exact polynomialNorm_constant_constant p c b
    · intro q hqdeg
      have hpq : p ≠ q := by
        intro heq
        subst q
        exact (Nat.lt_irrefl _ hqdeg)
      rw [norm_quotientUnit_reciprocity p q hpq, symbol_mul_left, symbol_pow_left]
      have hrec := polynomialNorm_polynomial_reciprocity p q hpq b
      rw [ih q.val.natDegree (hpdeg ▸ hqdeg) q rfl
        (quotientUnit q.val p.val (not_dvd_of_ne p q hpq)) b] at hrec
      exact hrec.trans (add_comm _ _)

/-- The equivalent mixed formula with the base-field unit in the first slot. -/
theorem polynomialNorm_constant_symbol [CharZero k] (p : MonicIrreducible k)
    (a : kˣ) (b : (AdjoinRoot p.val)ˣ) :
    polynomialNorm p (symbol
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom a) b) =
      symbol a (Units.map (Algebra.norm k) b) := by
  rw [symbol_skew, map_neg, polynomialNorm_symbol_constant, symbol_skew a]

end MilnorK.K3.PolynomialNorm
