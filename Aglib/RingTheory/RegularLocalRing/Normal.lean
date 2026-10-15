/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.RingTheory.RegularLocalRing.Parameters
public import Aglib.RingTheory.IntegralClosure.FractionRing

/-!
Scratch B01 LG-04: normality by induction on prime parameter quotients.
Full regular-local normality is the eventual target; no reduced/domain/normal
hypothesis is to be added to that final statement. Auxiliary lemmas below state
their own algebraic assumptions explicitly.

## Extraction basis

Transferred from `R5Lab.RingTheory.RegularLocalRing.Normal` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`9179c6d9d165e8a73305c56dd74032778ace37d6f0f9e9a69ff2e6500bb2294c`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
universe u v
open scoped nonZeroDivisors

namespace IsRegularLocalRing

open IsLocalRing

/-- In dimension at least two, one can choose a first prime parameter which
does not divide a given nonzero denominator. Prime avoidance uses the actual
minimal primes over the denominator and the single nonprime ideal `m²`; no
infinite residue-field assumption is used. -/
theorem exists_prime_parameter_not_dvd (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (d : ℕ) (hd : ringKrullDim R = (d + 2 : ℕ))
    (b : R) (hb : b ≠ 0) :
    ∃ p : R, p ∈ maximalIdeal R ∧ Prime p ∧ ¬p ∣ b ∧
      IsRegularLocalRing (R ⧸ Ideal.span {p}) ∧
      ringKrullDim (R ⧸ Ideal.span {p}) = (d + 1 : ℕ) := by
  classical
  have : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let m := maximalIdeal R
  let J : Ideal R := Ideal.span {b}
  have hsq : ¬m ≤ m ^ 2 := by
    intro h
    have hm : m = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m m
      m.fg_of_isNoetherianRing (by simpa only [smul_eq_mul, pow_two] using h)
      (by simp [m, IsLocalRing.jacobson_eq_maximalIdeal])
    have hz := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hm)
    rw [hd] at hz
    norm_cast at hz
  have hmin : ∀ P ∈ J.minimalPrimes, ¬m ≤ P := by
    intro P hP hle
    have he : m = P := (maximalIdeal.isMaximal R).eq_of_le hP.isPrime.ne_top hle
    have hh := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes J P hP
    have hh' : ringKrullDim R ≤ 1 := by
      rw [← maximalIdeal_height_eq_ringKrullDim, show maximalIdeal R = P from he]
      exact_mod_cast hh
    rw [hd] at hh'
    norm_cast at hh'
  let S : Set (Ideal R) := insert (m ^ 2) J.minimalPrimes
  have hfinite : S.Finite := (Ideal.finite_minimalPrimes_of_isNoetherianRing R J).insert _
  have hnot : ¬(m : Set R) ⊆ ⋃ P ∈ S, (P : Set R) := by
    rw [Ideal.subset_union_prime_finite hfinite (m ^ 2) (m ^ 2)
      (fun P hP hne _ => (Set.mem_insert_iff.mp hP).resolve_left hne |>.isPrime)]
    rintro ⟨P, hP, hle⟩
    rcases Set.mem_insert_iff.mp hP with rfl | hP
    · exact hsq hle
    · exact hmin P hP hle
  obtain ⟨p, hpm, hpS⟩ := Set.not_subset.mp hnot
  have hpm2 : p ∉ m ^ 2 := by
    intro h
    exact hpS (Set.mem_iUnion.mpr ⟨m ^ 2,
      Set.mem_iUnion.mpr ⟨Set.mem_insert _ _, h⟩⟩)
  have havoid : ∀ P ∈ J.minimalPrimes, p ∉ P := by
    intro P hP hpP
    exact hpS (Set.mem_iUnion.mpr ⟨P,
      Set.mem_iUnion.mpr ⟨Set.mem_insert_of_mem _ hP, hpP⟩⟩)
  have hp0 : p ≠ 0 := fun e => hpm2 (e ▸ (m ^ 2).zero_mem)
  obtain ⟨hq, hdim⟩ := IsRegularLocalRing.regularLocal_quotient_parameter R (d + 1)
    (by simpa only [Nat.add_assoc] using hd) p hpm hpm2
  have := hq
  have hdomain := IsRegularLocalRing.isDomain_of_regularLocal (R ⧸ Ideal.span {p})
  have hprimeIdeal : (Ideal.span {p}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdomain
  have hp : Prime p := (Ideal.span_singleton_prime hp0).mp hprimeIdeal
  have hpb : ¬p ∣ b := by
    intro hpb
    have := hprimeIdeal
    obtain ⟨P, hP, hPp⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem (Ideal.span {p})).mpr
        (Ideal.mem_span_singleton.mpr hpb))
    have hpP := havoid P hP
    have hPbot : P = ⊥ := by
      apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {p}) P
        P.fg_of_isNoetherianRing
      · intro z hz
        obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp (hPp hz)
        have hsP : s ∈ P := (hP.isPrime.mem_or_mem (hs ▸ hz)).resolve_left hpP
        rw [hs]
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self p) hsP
      · rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
        exact (Ideal.span_singleton_le_iff_mem _).mpr hpm
    have hbP : b ∈ P := hP.1.2 (Ideal.mem_span_singleton_self b)
    exact hb (show b ∈ (⊥ : Ideal R) from hPbot ▸ hbP)
  exact ⟨p, hpm, hp, hpb, hq, hdim⟩

/-- The low-dimensional base of the induction uses the actual regular-local
domain theorem and the principal-maximal-ideal characterization. -/
theorem isIntegrallyClosed_of_regularLocal_dimension_le_one (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hd : ringKrullDim R ≤ 1) : IsIntegrallyClosed R := by
  have : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  have he := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  have hc : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
    exact_mod_cast he.trans_le hd
  have : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 6 1).mp hc
  infer_instance

/-- A regular local ring of any finite dimension is integrally closed.
The induction uses normal prime-parameter quotients and the numerator ideal. -/
theorem isIntegrallyClosed_of_regularLocal_dimension (d : ℕ) (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hd : ringKrullDim R = (d : ℕ)) : IsIntegrallyClosed R := by
  induction d generalizing R with
  | zero => exact isIntegrallyClosed_of_regularLocal_dimension_le_one R (by rw [hd]; norm_num)
  | succ d ih =>
    cases d with
    | zero => exact isIntegrallyClosed_of_regularLocal_dimension_le_one R (by simpa using hd.le)
    | succ e =>
      have : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
      apply (isIntegrallyClosed_iff (FractionRing R)).mpr
      intro z hz
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R z
      have hb0 : b ≠ 0 := by simpa using hb
      obtain ⟨p, hpm, hp, hpb, hq, hdim⟩ := exists_prime_parameter_not_dvd R e
        (by simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hd) b hb0
      have := hq
      have : IsIntegrallyClosed (R ⧸ Ideal.span {p}) :=
        ih (R ⧸ Ideal.span {p}) (by simpa only [Nat.succ_eq_add_one] using hdim)
      obtain ⟨r, hr⟩ :=
        IsFractionRing.dvd_of_isIntegral_div_of_normal_parameter (FractionRing R) hp hpm hpb hz
      refine ⟨r, ?_⟩
      have hbF : algebraMap R (FractionRing R) b ≠ 0 := by
        simpa using (IsFractionRing.injective R (FractionRing R)).ne hb0
      rw [hr, map_mul, mul_div_cancel_left₀ _ hbF]

/-- General regular-local normality at Mathlib's exact regular-local interface. -/
theorem isIntegrallyClosed_of_regularLocal (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : IsIntegrallyClosed R :=
  isIntegrallyClosed_of_regularLocal_dimension (maximalIdeal R).spanFinrank R
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm

end IsRegularLocalRing
