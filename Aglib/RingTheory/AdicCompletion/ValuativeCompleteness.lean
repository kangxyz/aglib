/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.DiscreteValuationRing
public import Aglib.RingTheory.Valuation.Sequences
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# Sequential completeness of the actual completed DVR fraction field

No new completeness axiom is introduced.
The first lemma extracts ordinary sequential completeness from the native
`IsPrecomplete.prec` diagonal completeness property. The second translates a
Cauchy tail into the valuation ring; this avoids choosing a common denominator.
-/

@[expose] public noncomputable section

open scoped WithZero
open IsDedekindDomain.HeightOneSpectrum

namespace IsPrecomplete

/-- Ordinary ideal-adic Cauchy sequences converge. The input is the native
algebraic precompleteness property, not a topological completeness oracle. -/
theorem exists_limit_of_cauchy
    {A : Type*} [CommRing A] (I : Ideal A) [IsPrecomplete I A]
    (a : ℕ → A)
    (ha : ∀ k : ℕ, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, a m - a n ∈ I ^ k) :
    ∃ L : A, ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, a n - L ∈ I ^ k := by
  classical
  choose N hN using ha
  let d : ℕ → ℕ := fun k => (Finset.Iic k).sup N
  have hd (i k : ℕ) (hik : i ≤ k) : N i ≤ d k := by
    exact Finset.le_sup (by simpa only [Finset.mem_Iic] using hik)
  have hdiag {m n : ℕ} (hmn : m ≤ n) :
      a (d m) ≡ a (d n) [SMOD (I ^ m • ⊤ : Submodule A A)] := by
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using
      hN m (d m) (hd m m le_rfl) (d n) (hd m n hmn)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I A)
    (f := fun n => a (d n)) hdiag
  refine ⟨L, fun k => ⟨N k, fun n hn => ?_⟩⟩
  have h₁ : a n - a (d k) ∈ I ^ k := hN k n hn (d k) (hd k k le_rfl)
  have h₂ : a (d k) - L ∈ I ^ k := by
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hL k
  simpa only [sub_add_sub_cancel] using (I ^ k).add_mem h₁ h₂

end IsPrecomplete

namespace IsDiscreteValuationRing

/-- The fraction field of an adically precomplete DVR is sequentially complete
for its actual normalized valuation. Thresholds range over all nonzero values.

A Cauchy tail is translated by one of its terms into the valuation ring. Its
limit exists by `IsPrecomplete.prec`; translating back proves the assertion.
No finite residue-field, local-compactness or spherical-completeness assumption
occurs. -/
theorem fractionRing_exists_valuative_limit
    (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsPrecomplete (IsLocalRing.maximalIdeal A) A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (s : ℕ → K)
    (hs : ∀ γ : ℤᵐ⁰, γ ≠ 0 → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N,
        (maximalIdeal A).valuation K (s m - s n) < γ) :
    ∃ x : K, ∀ γ : ℤᵐ⁰, γ ≠ 0 → ∃ N : ℕ,
      ∀ n ≥ N, (maximalIdeal A).valuation K (s n - x) < γ := by
  classical
  let v : Valuation K ℤᵐ⁰ := (maximalIdeal A).valuation K
  obtain ⟨N, hN⟩ := hs 1 one_ne_zero
  have htail (n : ℕ) : ∃ a : A, algebraMap A K a = s (N + n) - s N := by
    apply exists_lift_of_le_one
    exact (hN (N + n) (Nat.le_add_right N n) N le_rfl).le
  choose a ha using htail
  have hac : ∀ k : ℕ, ∃ M : ℕ, ∀ m ≥ M, ∀ n ≥ M,
      a m - a n ∈ (IsLocalRing.maximalIdeal A) ^ k := by
    intro k
    obtain ⟨M, hM⟩ := hs (WithZero.exp (-(k : ℤ))) (by simp)
    refine ⟨M, fun m hm n hn => ?_⟩
    have hv : v (algebraMap A K (a m - a n)) ≤ WithZero.exp (-(k : ℤ)) := by
      have heq : algebraMap A K (a m - a n) = s (N + m) - s (N + n) := by
        rw [map_sub, ha m, ha n]
        ring
      rw [heq]
      exact (hM (N + m) (by omega) (N + n) (by omega)).le
    rw [show v (algebraMap A K (a m - a n)) =
      (maximalIdeal A).intValuation (a m - a n) from
      valuation_of_algebraMap (maximalIdeal A) (a m - a n)] at hv
    exact ((maximalIdeal A).intValuation_le_pow_iff_mem (a m - a n) k).mp hv
  obtain ⟨L, hL⟩ := IsPrecomplete.exists_limit_of_cauchy
    (IsLocalRing.maximalIdeal A) a hac
  refine ⟨algebraMap A K L + s N, fun γ hγ => ?_⟩
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt hγ
  obtain ⟨M, hM⟩ := hL k
  refine ⟨N + M, fun n hn => ?_⟩
  have hnm : M ≤ n - N := by omega
  have hnn : N + (n - N) = n := by omega
  have hv : v (algebraMap A K (a (n - N) - L)) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [show v (algebraMap A K (a (n - N) - L)) =
      (maximalIdeal A).intValuation (a (n - N) - L) from
      valuation_of_algebraMap (maximalIdeal A) (a (n - N) - L)]
    exact ((maximalIdeal A).intValuation_le_pow_iff_mem (a (n - N) - L) k).mpr
      (hM (n - N) hnm)
  have heq : algebraMap A K (a (n - N) - L) =
      s n - (algebraMap A K L + s N) := by
    rw [map_sub, ha, hnn]
    ring
  change v (s n - (algebraMap A K L + s N)) < γ
  rw [← heq]
  exact hv.trans_lt hk

/-- Packaged version of the genuine fraction-field completeness theorem. -/
theorem fractionRing_isSeqComplete
    (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsPrecomplete (IsLocalRing.maximalIdeal A) A]
    [Field K] [Algebra A K] [IsFractionRing A K] :
    ((maximalIdeal A).valuation K).IsSeqComplete := by
  intro s hs
  exact fractionRing_exists_valuative_limit A K s hs

end IsDiscreteValuationRing

namespace AdicCompletion

/-- Genuine valuative completeness of the fraction field of the literal
maximal-ideal adic completion of a domain DVR. All algebra maps and valuations
are the native ones. The precompleteness instance is supplied by Mathlib's
actual adic-completion theorem. -/
theorem fractionRing_exists_valuative_limit
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (s : ℕ → FractionRing (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (hs : ∀ γ : ℤᵐ⁰, γ ≠ 0 → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      (IsDiscreteValuationRing.maximalIdeal
        (AdicCompletion (IsLocalRing.maximalIdeal R) R)).valuation
        (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal R) R)) (s m - s n) < γ) :
    ∃ x : FractionRing (AdicCompletion (IsLocalRing.maximalIdeal R) R),
      ∀ γ : ℤᵐ⁰, γ ≠ 0 → ∃ N : ℕ, ∀ n ≥ N,
        (IsDiscreteValuationRing.maximalIdeal
          (AdicCompletion (IsLocalRing.maximalIdeal R) R)).valuation
          (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal R) R)) (s n - x) < γ := by
  exact IsDiscreteValuationRing.fractionRing_exists_valuative_limit
    (AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal R) R)) s hs

/-- The literal completed DVR fraction field satisfies the genuine sequential
valuative completeness interface used by finite Frobenius coefficient spaces. -/
theorem fractionRing_isSeqComplete
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ((IsDiscreteValuationRing.maximalIdeal
      (AdicCompletion (IsLocalRing.maximalIdeal R) R)).valuation
      (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal R) R))).IsSeqComplete := by
  intro s hs
  exact fractionRing_exists_valuative_limit R s hs

end AdicCompletion
