/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PrincipalUnitResidue

/-!
# A root-symbol recurrence for the constructed polynomial norm

The three actual finite residues of `{p,q,X}` and its infinity residue give
a Euclidean recurrence for root symbols. Factoring the reduced representative
of an arbitrary first entry reduces it to strictly smaller polynomial places,
the variable place, and base-field symbols. No unit or valuation hypothesis
on that arbitrary entry is imposed.

This is a prerequisite for a local norm argument. It does not assert that the
constructed norm preserves a principal-unit filtration, commutes with DVR
specialization, or is independent of its polynomial presentation.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.PolynomialNorm

open Polynomial PolynomialResidue MilnorK.K2

variable {k : Type*} [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

private theorem symbol3_pow_first {K : Type*} [Field K] (a b c : Kˣ) (n : ℕ) :
    symbol3 (a ^ n) b c = n • symbol3 a b c := by
  have h := congrArg (symbol3FixedLast c) (symbol_pow_left a b n)
  simpa only [symbol3FixedLast_symbol, map_nsmul] using h

/-- At infinity a monic polynomial can be replaced by the corresponding power
of the variable, even when either other entry has a zero or a pole. -/
theorem residue_monic_first (p : k[X]) (hp : p.Monic) (a b : (RatFunc k)ˣ) :
    InfinityResidue.residue k (symbol3 (polynomialUnit p hp.ne_zero) a b) =
      p.natDegree • InfinityResidue.residue k
        (symbol3 (InfinityResidue.variableUnit k) a b) := by
  have h := InfinityResidue.residue_monic_ratio p (X ^ p.natDegree) hp
    (monic_X.pow _) (by simp only [natDegree_X_pow]) a b
  have hpow : polynomialUnit (X ^ p.natDegree) (monic_X.pow p.natDegree).ne_zero =
      InfinityResidue.variableUnit k ^ p.natDegree := by
    apply Units.ext
    exact map_pow (algebraMap k[X] (RatFunc k)) X p.natDegree
  rw [symbol3_div_left, map_sub, hpow, symbol3_pow_first, map_nsmul] at h
  exact sub_eq_zero.mp h

/-- The sign at infinity in the three-place root recurrence is retained in
the original Milnor group, including its possible two-torsion. -/
theorem residue_polynomials_variable (p q : k[X]) (hp : p.Monic) (hq : q.Monic) :
    InfinityResidue.residue k (symbol3 (polynomialUnit p hp.ne_zero)
      (polynomialUnit q hq.ne_zero) (InfinityResidue.variableUnit k)) =
      -((p.natDegree * q.natDegree) • symbol (-1 : kˣ) (-1)) := by
  have hsign : InfinityResidue.constantUnit k (-1) = (-1 : (RatFunc k)ˣ) := by
    apply Units.ext
    simp only [InfinityResidue.constantUnit_coe, Units.val_neg, Units.val_one, map_neg, map_one]
  rw [residue_monic_first p hp, symbol3_cyclic_left,
    residue_monic_first q hq, symbol3_self_right, symbol3_self_left,
    ← hsign, InfinityResidue.residue_variable, smul_neg, smul_neg, mul_nsmul]
  rw [smul_comm]

/-- The only finite residues of `{p,q,X}` are the two root symbols and the
constant-coefficient symbol at the variable place. -/
theorem totalResidue_polynomials_variable [DecidableEq (MonicIrreducible k)]
    (p q : MonicIrreducible k) (hpq : p ≠ q)
    (hp0 : p.val.coeff 0 ≠ 0) (hq0 : q.val.coeff 0 ≠ 0) :
    totalResidue (symbol3 (polynomialUnit p.val p.property.2.ne_zero)
      (polynomialUnit q.val q.property.2.ne_zero) (InfinityResidue.variableUnit k)) =
      DFinsupp.single p (symbol (quotientUnit p.val q.val (not_dvd_of_ne q p hpq.symm))
        (rootUnit p hp0)) -
      DFinsupp.single q (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq))
        (rootUnit q hq0)) +
      DFinsupp.single (variablePlace k)
        (MilnorK.K2.map (algebraMap k (AdjoinRoot (variablePlace k).val))
          (symbol (constantCoeffUnit p hp0) (constantCoeffUnit q hq0))) := by
  classical
  apply DFinsupp.ext
  intro r
  rw [totalResidue_apply, DFinsupp.add_apply, DFinsupp.sub_apply]
  by_cases hrp : r = p
  · subst r
    rw [DFinsupp.single_eq_same, DFinsupp.single_eq_of_ne hpq,
      DFinsupp.single_eq_of_ne (ne_variablePlace p hp0), sub_zero, add_zero]
    exact residueAt_polynomial_units p.val q.val X _ _
      (not_dvd_of_ne q p hpq.symm) (not_dvd_variable p hp0)
  · rw [DFinsupp.single_eq_of_ne hrp]
    by_cases hrq : r = q
    · subst r
      rw [DFinsupp.single_eq_same, DFinsupp.single_eq_of_ne (ne_variablePlace q hq0),
        zero_sub, add_zero, symbol3_skew_left, map_neg]
      congr 1
      exact residueAt_polynomial_units q.val p.val X _ _
        (not_dvd_of_ne p q hpq) (not_dvd_variable q hq0)
    · rw [DFinsupp.single_eq_of_ne hrq, sub_zero, zero_add]
      by_cases hrX : r = variablePlace k
      · subst r
        rw [DFinsupp.single_eq_same, symbol3_cyclic]
        change residueAt (variablePlace k).val
          (symbol3 (polynomialUnit (variablePlace k).val X_ne_zero)
            (polynomialUnit p.val _) (polynomialUnit q.val _)) = _
        rw [residueAt_polynomial_units _ _ _ _ _
          (by simpa only [variablePlace, X_dvd_iff] using hp0)
          (by simpa only [variablePlace, X_dvd_iff] using hq0),
          quotientUnit_variable p.val hp0, quotientUnit_variable q.val hq0,
          MilnorK.K2.map_symbol]
        rfl
      · rw [DFinsupp.single_eq_of_ne hrX]
        exact residueAt_polynomial_units_zero r.val p.val q.val X _ _ X_ne_zero
          (not_dvd_of_ne p r (Ne.symm hrp)) (not_dvd_of_ne q r (Ne.symm hrq))
          (not_dvd_of_ne (variablePlace k) r (Ne.symm hrX))

/-- Euclidean reciprocity for root symbols, proved using the actual norm and
all three actual finite residues, rather than a canonical norm interface. -/
theorem polynomialNorm_root_reciprocity (p q : MonicIrreducible k) (hpq : p ≠ q)
    (hp0 : p.val.coeff 0 ≠ 0) (hq0 : q.val.coeff 0 ≠ 0) :
    polynomialNorm p
      (symbol (quotientUnit p.val q.val (not_dvd_of_ne q p hpq.symm)) (rootUnit p hp0)) =
      polynomialNorm q
        (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq)) (rootUnit q hq0)) -
      symbol (constantCoeffUnit p hp0) (constantCoeffUnit q hq0) +
      (p.val.natDegree * q.val.natDegree) • symbol (-1 : kˣ) (-1) := by
  classical
  have h := totalNorm_totalResidue
    (symbol3 (polynomialUnit p.val p.property.2.ne_zero)
      (polynomialUnit q.val q.property.2.ne_zero) (InfinityResidue.variableUnit k))
  rw [totalResidue_polynomials_variable p q hpq hp0 hq0, map_add, map_sub,
    totalNorm_single, totalNorm_single, totalNorm_single,
    polynomialNorm_variable_map_constants,
    residue_polynomials_variable p.val q.val p.property.1 q.property.1, neg_neg] at h
  apply eq_of_sub_eq_zero
  calc
    _ = (polynomialNorm p
        (symbol (quotientUnit p.val q.val (not_dvd_of_ne q p hpq.symm)) (rootUnit p hp0)) -
      polynomialNorm q
        (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq)) (rootUnit q hq0)) +
      symbol (constantCoeffUnit p hp0) (constantCoeffUnit q hq0)) -
      (p.val.natDegree * q.val.natDegree) • symbol (-1 : kˣ) (-1) := by abel
    _ = 0 := by rw [h, sub_self]

private theorem quotientUnit_mul (p : MonicIrreducible k) (a b : k[X])
    (ha : ¬ p.val ∣ a) (hb : ¬ p.val ∣ b) (hab : ¬ p.val ∣ a * b) :
    quotientUnit p.val (a * b) hab = quotientUnit p.val a ha * quotientUnit p.val b hb := by
  apply Units.ext
  exact map_mul (AdjoinRoot.mk p.val) a b

private theorem norm_root_prod_mem (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0)
    (S : Submodule ℤ (MilnorK.K2.Group k)) (s : Multiset k[X]) (hs : ¬ p.val ∣ s.prod)
    (hmem : ∀ a ∈ s, ∀ ha : ¬ p.val ∣ a,
      polynomialNorm p (symbol (quotientUnit p.val a ha) (rootUnit p hp0)) ∈ S) :
    polynomialNorm p (symbol (quotientUnit p.val s.prod hs) (rootUnit p hp0)) ∈ S := by
  induction s using Multiset.induction_on with
  | empty =>
    have hunit : quotientUnit p.val (0 : Multiset k[X]).prod hs = 1 := by
      apply Units.ext
      exact map_one (AdjoinRoot.mk p.val)
    rw [hunit, symbol_one_left, map_zero]
    exact S.zero_mem
  | cons a s ih =>
    simp only [Multiset.prod_cons] at hs ⊢
    have ha : ¬ p.val ∣ a := fun h => hs (dvd_mul_of_dvd_left h _)
    have hs' : ¬ p.val ∣ s.prod := fun h => hs (dvd_mul_of_dvd_right h _)
    rw [quotientUnit_mul p a s.prod ha hs' hs, symbol_mul_left, map_add]
    exact S.add_mem (hmem a (Multiset.mem_cons_self a s) ha)
      (ih hs' (fun c hc => hmem c (Multiset.mem_cons_of_mem hc)))

/-- A precise lower-degree criterion for the norm of `{b,root}` with arbitrary
`b`. The smaller-place terms retain both the constant-coefficient correction
and the degree-product sign. The factor `X` is handled by the actual diagonal
Milnor relation; it is not excluded by a nonzero-constant-term assumption on
the representative of `b`.

This is an algebraic induction criterion, not an assertion that a chosen
valuation submodule satisfies its smaller-place hypothesis. -/
theorem polynomialNorm_root_mem_of_lower_degree
    (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0) (S : Submodule ℤ (MilnorK.K2.Group k))
    (hconstant : ∀ c : kˣ,
      symbol c ((-1) ^ p.val.natDegree * constantCoeffUnit p hp0) ∈ S)
    (hlower : ∀ (q : MonicIrreducible k), q.val.natDegree < p.val.natDegree →
      ∀ (hq0 : q.val.coeff 0 ≠ 0) (hpq : p ≠ q),
      polynomialNorm q
        (symbol (quotientUnit q.val p.val (not_dvd_of_ne p q hpq)) (rootUnit q hq0)) -
      symbol (constantCoeffUnit p hp0) (constantCoeffUnit q hq0) +
      (p.val.natDegree * q.val.natDegree) • symbol (-1 : kˣ) (-1) ∈ S)
    (b : (AdjoinRoot p.val)ˣ) :
    polynomialNorm p (symbol b (rootUnit p hp0)) ∈ S := by
  classical
  have hc (c : kˣ) : polynomialNorm p
      (symbol (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom c)
        (rootUnit p hp0)) ∈ S := by
    rw [symbol_skew, map_neg, polynomialNorm_root_constant_coefficient,
      ← symbol_skew c]
    exact hconstant c
  let B := DegreeFiltration.reducedRepresentative p.val p.property.1 b
  have hB : B ≠ 0 := DegreeFiltration.reducedRepresentative_ne_zero p.val p.property.1 b
  have hBd : B.natDegree < p.val.natDegree :=
    DegreeFiltration.reducedRepresentative_natDegree_lt p.val p.property.1 b
  have hBp : ¬ p.val ∣ B := p.property.1.not_dvd_of_natDegree_lt hB hBd
  let s := UniqueFactorizationMonoid.normalizedFactors B
  have hfactor : C B.leadingCoeff * s.prod = B :=
    Polynomial.leadingCoeff_mul_prod_normalizedFactors B
  have hs : ¬ p.val ∣ s.prod := by
    intro h
    apply hBp
    rw [← hfactor]
    exact dvd_mul_of_dvd_right h _
  have hmem : ∀ a ∈ s, ∀ ha : ¬ p.val ∣ a,
      polynomialNorm p (symbol (quotientUnit p.val a ha) (rootUnit p hp0)) ∈ S := by
    intro a ha hap
    obtain ⟨hai, ham, hadvd⟩ := (Polynomial.mem_normalizedFactors_iff hB).mp ha
    let q : MonicIrreducible k := ⟨a, ham, hai⟩
    have hqd : q.val.natDegree < p.val.natDegree :=
      (Polynomial.natDegree_le_of_dvd hadvd hB).trans_lt hBd
    have hpq : p ≠ q := by
      intro heq
      exact (Nat.lt_irrefl p.val.natDegree) (heq ▸ hqd)
    by_cases hq0 : q.val.coeff 0 = 0
    · have hqX : q = variablePlace k := by
        by_contra h
        exact not_dvd_of_ne q (variablePlace k) h (X_dvd_iff.mpr hq0)
      have hroot : quotientUnit p.val a hap = rootUnit p hp0 := by
        apply Units.ext
        change AdjoinRoot.mk p.val q.val = AdjoinRoot.mk p.val X
        rw [congrArg Subtype.val hqX]
      have hneg : Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom (-1) =
          (-1 : (AdjoinRoot p.val)ˣ) := by
        apply Units.ext
        change algebraMap k (AdjoinRoot p.val) (-1) = -1
        rw [map_neg, map_one]
      rw [hroot, symbol_self, symbol_skew, map_neg]
      rw [← hneg]
      exact S.neg_mem (hc (-1))
    · change polynomialNorm p
        (symbol (quotientUnit p.val q.val hap) (rootUnit p hp0)) ∈ S
      rw [polynomialNorm_root_reciprocity p q hpq hp0 hq0]
      exact hlower q hqd hq0 hpq
  have hprod := norm_root_prod_mem p hp0 S s hs hmem
  let c : kˣ := Units.mk0 B.leadingCoeff (leadingCoeff_ne_zero.mpr hB)
  have hcp : ¬ p.val ∣ C B.leadingCoeff := not_dvd_constant p c
  have hunit : quotientUnit p.val B hBp =
      quotientUnit p.val (C B.leadingCoeff) hcp * quotientUnit p.val s.prod hs := by
    apply Units.ext
    change AdjoinRoot.mk p.val B =
      AdjoinRoot.mk p.val (C B.leadingCoeff) * AdjoinRoot.mk p.val s.prod
    rw [← map_mul, hfactor]
  have hb : quotientUnit p.val B hBp = b :=
    DegreeFiltration.quotientUnit_reducedRepresentative p.val p.property.1 b
  rw [← hb, hunit, symbol_mul_left, map_add]
  apply S.add_mem _ hprod
  change polynomialNorm p
    (symbol (quotientUnit p.val (C (c : k)) (not_dvd_constant p c)) (rootUnit p hp0)) ∈ S
  rw [quotientUnit_constant]
  exact hc c

end MilnorK.K3.PolynomialNorm
