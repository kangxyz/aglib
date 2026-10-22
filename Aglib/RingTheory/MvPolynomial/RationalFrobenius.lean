/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.FrobeniusDecomposition
public import Aglib.FieldTheory.SeparablyGenerated.FrobeniusCriterion
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rational Frobenius transport from finite monomial independence

All actions are supplied actual algebra maps. The only input concerning the
extension field is independence of finite coefficient families times bounded
monomials. Native fraction-ring linear-independence transport clears denominators.
-/

@[expose] public noncomputable section

namespace MvPolynomial

/-- Finite monomial Frobenius independence, expressed without a global p-basis.
The map from the polynomial ring is the supplied algebra map, not an abstract
identification of the variables. -/
def FiniteMonomialFrobeniusIndependent
    {k L σ : Type*} [Field k] [Field L] [Algebra (MvPolynomial σ k) L]
    (p : ℕ) [ExpChar k p] [ExpChar L p] : Prop :=
  ∀ (b : Finset k) (r : Finset (σ →₀ ℕ)),
    LinearIndependent (frobenius k p).fieldRange ((↑) : b → k) →
    (∀ e ∈ r, ∀ x, e x < p) →
    LinearIndependent (frobenius L p).fieldRange
      (fun q : r × b => algebraMap (MvPolynomial σ k) L (monomial q.1.val q.2.val))

/-- Convert the independence contract into the finite-sum form used by
polynomial Frobenius decomposition. -/
lemma FiniteMonomialFrobeniusIndependent.sum_eq_zero
    {k L σ : Type*} [Field k] [Field L] [Algebra (MvPolynomial σ k) L]
    (p : ℕ) [ExpChar k p] [ExpChar L p]
    (H : FiniteMonomialFrobeniusIndependent (k := k) (L := L) (σ := σ) p)
    (b : Finset k) (r : Finset (σ →₀ ℕ))
    (hb : LinearIndependent (frobenius k p).fieldRange ((↑) : b → k))
    (hr : ∀ e ∈ r, ∀ x, e x < p) (g : r → b → L)
    (h : ∑ e : r, ∑ j : b,
      algebraMap (MvPolynomial σ k) L (monomial e.val j.val) * g e j ^ p = 0) :
    ∀ e j, g e j = 0 := by
  classical
  let c : r × b → (frobenius L p).fieldRange :=
    fun q => (frobenius L p).rangeRestrictField (g q.1 q.2)
  have hc : ∑ q : r × b, c q •
      algebraMap (MvPolynomial σ k) L (monomial q.1.val q.2.val) = 0 := by
    change ∑ q : r × b, g q.1 q.2 ^ p *
      algebraMap (MvPolynomial σ k) L (monomial q.1.val q.2.val) = 0
    simpa only [Fintype.sum_prod_type, mul_comm] using h
  have hz := Fintype.linearIndependent_iff.mp (H b r hb hr) c hc
  intro e j
  have hh : g e j ^ p = 0 := congrArg Subtype.val (hz (e, j))
  exact eq_zero_of_pow_eq_zero hh

/-- Polynomial-linear independence survives Frobenius under the finite
coefficient-times-monomial contract. No finite p-rank or finite variable type is used. -/
lemma linearIndependent_pow_of_finiteMonomialFrobeniusIndependent
    {k L σ ι : Type*} [Field k] [Field L] [Algebra (MvPolynomial σ k) L]
    [Finite ι] (p : ℕ) (hp : p ≠ 0) [ExpChar k p] [ExpChar L p]
    (H : FiniteMonomialFrobeniusIndependent (k := k) (L := L) (σ := σ) p)
    (f : ι → L) (hf : LinearIndependent (MvPolynomial σ k) f) :
    LinearIndependent (MvPolynomial σ k) (fun i => f i ^ p) := by
  classical
  let := Fintype.ofFinite ι
  let m := algebraMap (MvPolynomial σ k) L
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  obtain ⟨b, r, hb, hr, Q, hQ⟩ :=
    exists_polynomial_frobenius_decomposition p hp c
  let g (e : r) (j : b) : L := ∑ i, m (Q i j e) * f i
  have hrel : ∑ e : r, ∑ j : b,
      m (monomial e.val j.val) * g e j ^ p = 0 := by
    let A (e : r) (j : b) (i : ι) : L :=
      m (monomial e.val j.val) * (m (Q i j e) * f i) ^ p
    calc
      _ = ∑ e : r, ∑ j : b, ∑ i, A e j i := by
        simp only [g, A, sum_pow_char p, Finset.mul_sum]
      _ = ∑ e : r, ∑ i, ∑ j : b, A e j i := by
        apply Finset.sum_congr rfl
        intro e he
        exact Finset.sum_comm
      _ = ∑ i, ∑ e : r, ∑ j : b, A e j i := Finset.sum_comm
      _ = ∑ i, m (c i) * f i ^ p := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hQ i, map_sum]
        simp only [A, map_sum, map_mul, map_pow, Finset.sum_mul, mul_pow, mul_assoc]
      _ = 0 := by simpa only [Algebra.smul_def] using hc
  have hg := H.sum_eq_zero p b r hb hr g hrel
  have hQ0 (i : ι) (j : b) (e : r) : Q i j e = 0 := by
    apply Fintype.linearIndependent_iff.mp hf (fun i => Q i j e) _ i
    simpa only [g, Algebra.smul_def] using hg e j
  intro i
  rw [hQ i]
  simp only [hQ0, zero_pow hp, mul_zero, Finset.sum_const_zero]

/-- The rational-function action must extend the actual polynomial action.
Native fraction-ring transport handles arbitrary rational denominators. -/
lemma linearIndependent_pow_over_fractionRing_of_finiteMonomialFrobeniusIndependent
    {k L F σ ι : Type*} [Field k] [Field L] [Field F]
    [Algebra (MvPolynomial σ k) L] [Algebra (MvPolynomial σ k) F]
    [IsFractionRing (MvPolynomial σ k) F] [Algebra F L]
    [IsScalarTower (MvPolynomial σ k) F L] [Finite ι]
    (p : ℕ) (hp : p ≠ 0) [ExpChar k p] [ExpChar L p]
    (H : FiniteMonomialFrobeniusIndependent (k := k) (L := L) (σ := σ) p)
    (f : ι → L) (hf : LinearIndependent F f) :
    LinearIndependent F (fun i => f i ^ p) := by
  apply (LinearIndependent.iff_fractionRing (MvPolynomial σ k) F).mp
  exact linearIndependent_pow_of_finiteMonomialFrobeniusIndependent p hp H f
    ((LinearIndependent.iff_fractionRing (MvPolynomial σ k) F).mpr hf)

/-- Close the actual rational-function extension using the finite Frobenius
criterion; the hard valued-field input is exactly the monomial contract. -/
lemma isGeometricallyReduced_fractionRing_of_finiteMonomialFrobeniusIndependent
    {k L F σ : Type*} [Field k] [Field L] [Field F]
    [Algebra (MvPolynomial σ k) L] [Algebra (MvPolynomial σ k) F]
    [IsFractionRing (MvPolynomial σ k) F] [Algebra F L]
    [IsScalarTower (MvPolynomial σ k) F L]
    (p : ℕ) (hp : p.Prime) [ExpChar k p] [ExpChar F p] [ExpChar L p]
    (H : FiniteMonomialFrobeniusIndependent (k := k) (L := L) (σ := σ) p) :
    Algebra.IsGeometricallyReduced F L := by
  apply Algebra.isGeometricallyReduced_of_linearIndependent_pow p hp
  intro n f hf
  exact linearIndependent_pow_over_fractionRing_of_finiteMonomialFrobeniusIndependent
    p hp.ne_zero H f hf

end MvPolynomial
