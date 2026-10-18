/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Balanced polynomial fractions in a simple field extension

A linear map from two spaces of bounded-degree polynomials to the root field
has a nonzero kernel when the sum of their dimensions exceeds the extension
degree. Injectivity of low-degree evaluation makes both entries nonzero.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k : Type*} [Field k] {p : k[X]} [Fact (Irreducible p)]

/-- The elementary dimension argument for polynomial fractions, with arbitrary
bounds whose two polynomial spaces have total dimension larger than the field. -/
theorem exists_fraction_of_degree_bounds (hp : p.Monic) (a b : ℕ)
    (ha : a < p.natDegree) (hb : b < p.natDegree)
    (hab : p.natDegree < a + b + 2) (x : AdjoinRoot p) (hx : x ≠ 0) :
    ∃ A B : k[X], A ≠ 0 ∧ B ≠ 0 ∧ A.natDegree ≤ a ∧ B.natDegree ≤ b ∧
      x = mk p A / mk p B := by
  let V := degreeLT k (a + 1) × degreeLT k (b + 1)
  let f : V →ₗ[k] AdjoinRoot p :=
    { toFun := fun v => aeval (root p) v.1.1 - x * aeval (root p) v.2.1
      map_add' := by
        intro u v
        change aeval (root p) (u.1.1 + v.1.1) -
          x * aeval (root p) (u.2.1 + v.2.1) = _
        simp only [map_add, mul_add]
        abel
      map_smul' := by
        intro c v
        change aeval (root p) (c • v.1.1) - x * aeval (root p) (c • v.2.1) =
          c • (aeval (root p) v.1.1 - x * aeval (root p) v.2.1)
        simp only [map_smul, smul_sub, mul_smul_comm] }
  let : Module.Finite k (AdjoinRoot p) := Module.Finite.of_basis (powerBasis hp.ne_zero).basis
  have hdimV : Module.finrank k V = a + b + 2 := by
    rw [Module.finrank_eq_card_basis (degreeLT.basisProd k (a + 1) (b + 1))]
    simp only [Fintype.card_fin]
    omega
  have hdim : Module.finrank k (AdjoinRoot p) = p.natDegree :=
    (powerBasis hp.ne_zero).finrank
  have hninj : ¬ Function.Injective f := by
    intro hf
    have h := f.finrank_le_finrank_of_injective hf
    rw [hdimV, hdim] at h
    omega
  obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp hninj
  let w := u - v
  have hw : w ≠ 0 := sub_ne_zero.mpr hne
  have hfw : f w = 0 := by simp only [w, map_sub, huv, sub_self]
  have heq : mk p w.1.1 = x * mk p w.2.1 := by
    change aeval (root p) w.1.1 - x * aeval (root p) w.2.1 = 0 at hfw
    simpa only [aeval_eq] using sub_eq_zero.mp hfw
  have hAdeg : w.1.1.natDegree ≤ a := by
    by_cases hz : w.1.1 = 0
    · simp [hz]
    exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hz).2
      (mem_degreeLT.mp w.1.2))
  have hBdeg : w.2.1.natDegree ≤ b := by
    by_cases hz : w.2.1 = 0
    · simp [hz]
    exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hz).2
      (mem_degreeLT.mp w.2.2))
  have hB : w.2.1 ≠ 0 := by
    intro hz
    have he : mk p w.1.1 = 0 := by simpa only [hz, map_zero, mul_zero] using heq
    have hA : w.1.1 = 0 := by
      by_contra hA
      exact mk_ne_zero_of_natDegree_lt hp hA (hAdeg.trans_lt ha) he
    apply hw
    exact Prod.ext (Subtype.ext hA) (Subtype.ext hz)
  have hBeval : mk p w.2.1 ≠ 0 := mk_ne_zero_of_natDegree_lt hp hB (hBdeg.trans_lt hb)
  have hA : w.1.1 ≠ 0 := by
    intro hz
    exact (mul_ne_zero hx hBeval) (by simpa only [hz, map_zero] using heq.symm)
  exact ⟨w.1.1, w.2.1, hA, hB, hAdeg, hBdeg,
    (eq_div_iff hBeval).2 heq.symm⟩

/-- Every nonzero element has a balanced polynomial fraction representative.
For degree one both polynomials are nonzero constants. -/
theorem exists_balanced_fraction (hp : p.Monic) (x : AdjoinRoot p) (hx : x ≠ 0) :
    ∃ A B : k[X], A ≠ 0 ∧ B ≠ 0 ∧ A.natDegree ≤ p.natDegree / 2 ∧
      B.natDegree ≤ (p.natDegree - 1) / 2 ∧ x = mk p A / mk p B := by
  have hn : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  apply exists_fraction_of_degree_bounds hp (p.natDegree / 2) ((p.natDegree - 1) / 2)
    (by omega) (by omega) (by omega) x hx

end AdjoinRoot

namespace Polynomial

variable {k : Type*} [Field k]

/-- Scaling one polynomial to the leading coefficient of another cancels the
highest-degree terms, including the possibility that the difference is zero. -/
theorem degree_sub_leadingRatio_mul_lt {A C : k[X]} (hA : A ≠ 0) (hC : C ≠ 0)
    (hd : A.natDegree = C.natDegree) :
    (C - Polynomial.C (C.leadingCoeff / A.leadingCoeff) * A).degree < C.degree := by
  have hAl : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hCl : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hC
  have hl : C.leadingCoeff / A.leadingCoeff ≠ 0 := div_ne_zero hCl hAl
  refine degree_sub_lt_left ?_ hC ?_
  · rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hl),
      degree_eq_natDegree hA, degree_eq_natDegree hC, hd]
  · rw [leadingCoeff_mul, leadingCoeff_C, div_mul_cancel₀ _ hAl]

end Polynomial
