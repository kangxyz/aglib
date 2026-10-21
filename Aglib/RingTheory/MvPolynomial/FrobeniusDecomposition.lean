/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Finite Frobenius decomposition of multivariate polynomials

A finite family of polynomials decomposes using a common finite independent
coefficient family over the Frobenius subfield and bounded exponent remainders.
-/

@[expose] public noncomputable section

namespace Algebra

/-- A finite coefficient set has a finite independent spanning family over the
literal p-th-power subfield, with each coordinate exhibited as a p-th power. -/
lemma exists_finite_frobenius_coordinates
    {k : Type*} [Field k] (p : ℕ) [ExpChar k p] (s : Finset k) :
    ∃ b : Finset k,
      LinearIndependent (frobenius k p).fieldRange ((↑) : b → k) ∧
      ∀ c ∈ s, ∃ d : b → k, ∑ j : b, (j : k) * (d j) ^ p = c := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ :=
    exists_linearIndependent (frobenius k p).fieldRange (s : Set k)
  lift b to Finset k using s.finite_toSet.subset hbs
  refine ⟨b, hli, ?_⟩
  intro c hc
  have hmem : c ∈ Submodule.span (frobenius k p).fieldRange (b : Set k) := by
    rw [hspan]
    exact Submodule.subset_span hc
  obtain ⟨a, ha⟩ := Submodule.mem_span_finset'.mp hmem
  let d (j : b) : k := (frobenius k p).rangeRestrictFieldEquiv.symm (a j)
  refine ⟨d, ?_⟩
  have hd (j : b) : d j ^ p = (a j : k) :=
    (frobenius k p).rangeRestrictFieldEquiv_apply_symm_apply (a j)
  simpa only [hd, mul_comm, Subfield.smul_def, smul_eq_mul] using ha

end Algebra

namespace MvPolynomial

/-- Pointwise quotient of a monomial exponent vector by the given natural number. -/
def exponentQuotient {σ : Type*} (p : ℕ) (n : σ →₀ ℕ) : σ →₀ ℕ :=
  n.mapRange (fun a => a / p) (Nat.zero_div p)

/-- Pointwise remainder of a monomial exponent vector modulo the given natural number. -/
def exponentRemainder {σ : Type*} (p : ℕ) (n : σ →₀ ℕ) : σ →₀ ℕ :=
  n.mapRange (fun a => a % p) (Nat.zero_mod p)

lemma exponentRemainder_add_smul_quotient {σ : Type*} (p : ℕ) (n : σ →₀ ℕ) :
    exponentRemainder p n + p • exponentQuotient p n = n := by
  ext x
  simp only [exponentRemainder, exponentQuotient, Finsupp.add_apply,
    Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Nat.mod_add_div (n x) p

lemma exponentRemainder_lt {σ : Type*} (p : ℕ) (hp : 0 < p) (n : σ →₀ ℕ) (x : σ) :
    exponentRemainder p n x < p := Nat.mod_lt _ hp

/-- The elementary monomial identity behind finite Frobenius decomposition. -/
lemma monomial_frobenius_decomposition
    {k σ : Type*} [Field k] (p : ℕ) (n : σ →₀ ℕ) (b d : k) :
    MvPolynomial.monomial (exponentRemainder p n) b *
        (MvPolynomial.monomial (exponentQuotient p n) d) ^ p =
      MvPolynomial.monomial n (b * d ^ p) := by
  rw [MvPolynomial.monomial_pow, MvPolynomial.monomial_mul_monomial,
    exponentRemainder_add_smul_quotient]

/-- Group a polynomial's given finite coefficient coordinates by exponent remainder.
The hypotheses are elementary coefficient data, not a separability assumption. -/
lemma polynomial_frobenius_decomposition_of_coordinates
    {k σ : Type*} [Field k] (p : ℕ) (hp : p ≠ 0) [ExpChar k p]
    (P : MvPolynomial σ k) (b : Finset k) (r : Finset (σ →₀ ℕ))
    (d : (σ →₀ ℕ) → b → k)
    (hd : ∀ n ∈ P.support, ∑ j : b, (j : k) * (d n j) ^ p = P.coeff n)
    (hr : ∀ n ∈ P.support, exponentRemainder p n ∈ r) :
    ∃ Q : b → r → MvPolynomial σ k,
      P = ∑ e : r, ∑ j : b, MvPolynomial.monomial (e : σ →₀ ℕ) (j : k) * Q j e ^ p := by
  classical
  let Q (j : b) (e : r) : MvPolynomial σ k :=
    ∑ n ∈ P.support, if exponentRemainder p n = e then
      MvPolynomial.monomial (exponentQuotient p n) (d n j) else 0
  have hQ (j : b) :
      ∑ e : r, MvPolynomial.monomial (e : σ →₀ ℕ) (j : k) * Q j e ^ p =
      ∑ n ∈ P.support, MvPolynomial.monomial n ((j : k) * d n j ^ p) := by
    let : ExpChar (MvPolynomial σ k) p := expChar_of_injective_ringHom
      (MvPolynomial.C_injective (σ := σ) (R := k)) p
    simp only [Q, sum_pow_char p, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    let e₀ : r := ⟨exponentRemainder p n, hr n hn⟩
    rw [Finset.sum_eq_single e₀]
    · simpa only [e₀, ite_eq_left rfl, ite_true] using
        monomial_frobenius_decomposition p n (j : k) (d n j)
    · intro e he hne
      have hnr : exponentRemainder p n ≠ (e : σ →₀ ℕ) := by
        intro heq
        exact hne (Subtype.ext heq.symm)
      simp only [ite_eq_right hnr, zero_pow hp, mul_zero]
    · simp
  refine ⟨Q, ?_⟩
  rw [Finset.sum_comm]
  simp_rw [hQ]
  rw [Finset.sum_comm]
  conv_lhs => rw [MvPolynomial.as_sum P]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← map_sum, hd n hn]

/-- Simultaneous finite Frobenius decomposition. Only coefficients occurring in the
input polynomials are used; no infinite basis or finiteness of σ is required. -/
lemma exists_polynomial_frobenius_decomposition
    {k σ ι : Type*} [Field k] [Finite ι]
    (p : ℕ) (hp : p ≠ 0) [ExpChar k p] (P : ι → MvPolynomial σ k) :
    ∃ (b : Finset k) (r : Finset (σ →₀ ℕ)),
      LinearIndependent (frobenius k p).fieldRange ((↑) : b → k) ∧
      (∀ e ∈ r, ∀ x, e x < p) ∧
      ∃ Q : ι → b → r → MvPolynomial σ k,
        ∀ i, P i = ∑ e : r, ∑ j : b,
          MvPolynomial.monomial (e : σ →₀ ℕ) (j : k) * Q i j e ^ p := by
  classical
  let := Fintype.ofFinite ι
  let s : Finset k := Finset.univ.biUnion fun i => (P i).support.image (P i).coeff
  let r : Finset (σ →₀ ℕ) :=
    Finset.univ.biUnion fun i => (P i).support.image (exponentRemainder p)
  obtain ⟨b, hb, hcoords⟩ := Algebra.exists_finite_frobenius_coordinates p s
  have hc : ∀ i n, ∃ d : b → k,
      n ∈ (P i).support → ∑ j : b, (j : k) * (d j) ^ p = (P i).coeff n := by
    intro i n
    by_cases hn : n ∈ (P i).support
    · have hmem : (P i).coeff n ∈ s :=
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩
      obtain ⟨d, hd⟩ := hcoords _ hmem
      exact ⟨d, fun _ => hd⟩
    · exact ⟨fun _ => 0, fun h => (hn h).elim⟩
  choose d hd using hc
  have hr (i : ι) (n : σ →₀ ℕ) (hn : n ∈ (P i).support) :
      exponentRemainder p n ∈ r :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩
  choose Q hQ using fun i => polynomial_frobenius_decomposition_of_coordinates
    p hp (P i) b r (d i) (hd i) (hr i)
  refine ⟨b, r, hb, ?_, Q, hQ⟩
  intro e he x
  obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp he
  exact exponentRemainder_lt p (Nat.pos_of_ne_zero hp) n x

end MvPolynomial
