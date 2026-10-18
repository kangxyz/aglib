/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialResidueBaseChange
public import Mathlib.Algebra.BigOperators.Associated

/-!
# Finite polynomial places under arbitrary coefficient extension

A target polynomial place need not contract to a finite source place. If it
divides the image of a nonzero source polynomial, normalized factorization
does produce a monic irreducible source polynomial below it. That source
polynomial is unique. Otherwise every nonzero source polynomial stays a unit
at the target place. No algebraicity hypothesis on the coefficient extension
is imposed.
-/

@[expose] public noncomputable section

namespace Polynomial.LocalResidue

variable {k L : Type*} [Field k] [Field L]

/-- A prime target factor of a nonzero coefficient image lies over an actual
monic irreducible factor of the source polynomial. -/
theorem exists_monic_irreducible_dvd_of_dvd_map (φ : k →+* L) (q : L[X])
    (hq : Irreducible q) (a : k[X]) (ha : a ≠ 0) (hqa : q ∣ a.map φ) :
    ∃ p : k[X], p.Monic ∧ Irreducible p ∧ p ∣ a ∧ q ∣ p.map φ := by
  classical
  have hfactor := congrArg (Polynomial.map φ)
    (Polynomial.leadingCoeff_mul_prod_normalizedFactors a)
  rw [Polynomial.map_mul] at hfactor
  rw [← hfactor] at hqa
  rcases hq.prime.dvd_or_dvd hqa with hc | hs
  · have hu : IsUnit ((C a.leadingCoeff).map φ) := by
      rw [Polynomial.map_C]
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by
        simpa only [map_zero] using φ.injective.ne (Polynomial.leadingCoeff_ne_zero.mpr ha)))
    exact (hq.not_isUnit (isUnit_of_dvd_unit hc hu)).elim
  · have hs' : q ∣ ((UniqueFactorizationMonoid.normalizedFactors a).map
        (Polynomial.map φ)).prod := by
      change q ∣ (Polynomial.mapRingHom φ)
        (UniqueFactorizationMonoid.normalizedFactors a).prod at hs
      rw [map_multiset_prod] at hs
      exact hs
    obtain ⟨p, hp, hqp⟩ := hq.prime.exists_mem_multiset_map_dvd hs'
    obtain ⟨hpi, hpm, hpa⟩ := (Polynomial.mem_normalizedFactors_iff ha).mp hp
    exact ⟨p, hpm, hpi, hpa, hqp⟩

/-- Two monic irreducible source polynomials below the same target place agree. -/
theorem monic_irreducible_eq_of_dvd_map (φ : k →+* L) (p r : k[X]) (q : L[X])
    [Fact (Irreducible p)] [Fact (Irreducible r)] [Fact (Irreducible q)]
    (hp : p.Monic) (hr : r.Monic) (hqp : q ∣ p.map φ) (hqr : q ∣ r.map φ) :
    p = r := by
  have hideal : primeIdeal p = primeIdeal r :=
    (primeIdeal_eq_comap φ p q hqp).trans (primeIdeal_eq_comap φ r q hqr).symm
  have hpr : p ∣ r := by
    apply Ideal.mem_span_singleton.mp
    change r ∈ primeIdeal p
    rw [hideal]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hrp : r ∣ p := by
    apply Ideal.mem_span_singleton.mp
    change p ∈ primeIdeal r
    rw [← hideal]
    exact Ideal.subset_span (Set.mem_singleton p)
  exact Polynomial.eq_of_monic_of_associated hp hr (associated_of_dvd_dvd hpr hrp)

/-- Every target place either lies over a finite source place, or divides no
nonzero source polynomial. The second case includes zero contraction. -/
theorem finite_place_or_no_polynomial_divisor (φ : k →+* L) (q : L[X])
    (hq : Irreducible q) :
    (∃ p : k[X], p.Monic ∧ Irreducible p ∧ q ∣ p.map φ) ∨
      (∀ a : k[X], a ≠ 0 → ¬q ∣ a.map φ) := by
  classical
  by_cases h : ∃ a : k[X], a ≠ 0 ∧ q ∣ a.map φ
  · obtain ⟨a, ha, hqa⟩ := h
    obtain ⟨p, hpm, hpi, _, hqp⟩ :=
      exists_monic_irreducible_dvd_of_dvd_map φ q hq a ha hqa
    exact Or.inl ⟨p, hpm, hpi, hqp⟩
  · exact Or.inr fun a ha hqa => h ⟨a, ha, hqa⟩

end Polynomial.LocalResidue
