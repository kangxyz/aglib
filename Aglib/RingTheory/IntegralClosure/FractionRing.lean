/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Integral fractions and normal parameter quotients

Over a Noetherian domain, a common bounded denominator characterizes integral fractions in a
specified fraction field. Prime factors can be canceled under the stated nondivisibility
conditions. A normal prime-parameter quotient controls integral numerators in the local case; no
regular-local hypothesis is needed for these helpers.

## Extraction basis

Transferred subsets of `R5Lab.RingTheory.RegularLocalRing.Normal` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, source SHA-256
`9179c6d9d165e8a73305c56dd74032778ace37d6f0f9e9a69ff2e6500bb2294c`. Objects, universes,
canonical maps and
actual premises are retained; declarations use native mathematical namespaces.
-/

@[expose] public section

noncomputable section

universe u v
open scoped nonZeroDivisors
namespace IsFractionRing

section Fractions
variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- A bounded common denominator for every power characterizes integral fractions. -/
theorem isIntegral_div_iff_exists_dvd (a b : R) (hb : b ≠ 0) :
    IsIntegral R (algebraMap R K a / algebraMap R K b) ↔
      ∃ c : R, c ≠ 0 ∧ ∀ n : ℕ, b ^ n ∣ c * a ^ n := by
  have hinj := IsFractionRing.injective R K
  have hbK : algebraMap R K b ≠ 0 := by simpa using hinj.ne hb
  constructor
  · intro h
    obtain ⟨c, hc, hcn⟩ := h.isAlmostIntegral
    refine ⟨c, by simpa using hc, fun n => ?_⟩
    obtain ⟨d, hd⟩ := hcn n
    refine ⟨d, hinj ?_⟩
    simp only [map_mul, map_pow]
    rw [hd, Algebra.smul_def, div_pow]
    field_simp
  · rintro ⟨c, hc, hcn⟩
    apply IsAlmostIntegral.isIntegral
    refine ⟨c, by simpa using hc, fun n => ?_⟩
    obtain ⟨d, hd⟩ := hcn n
    refine ⟨d, ?_⟩
    rw [Algebra.smul_def, div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero n hbK)]
    simpa only [map_mul, map_pow, mul_comm] using congrArg (algebraMap R K) hd.symm

omit [IsNoetherianRing R] in
/-- A prime factor outside the divisor cancels from a divisibility relation. -/
theorem _root_.Prime.dvd_of_prime_mul_dvd {p b c : R} (hp : Prime p) (hpb : ¬p ∣ b)
    (h : b ∣ p * c) : b ∣ c := by
  obtain ⟨d, hd⟩ := h
  have hpd : p ∣ d := (hp.dvd_mul.mp (hd ▸ dvd_mul_right p c)).resolve_left hpb
  obtain ⟨e, rfl⟩ := hpd
  refine ⟨e, mul_left_cancel₀ hp.ne_zero ?_⟩
  simpa only [mul_assoc, mul_left_comm] using hd

omit [IsNoetherianRing R] in
theorem _root_.Prime.dvd_of_prime_pow_mul_dvd {p b c : R} (hp : Prime p) (hpb : ¬p ∣ b)
    (n : ℕ) (h : b ∣ p ^ n * c) : b ∣ c := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply Prime.dvd_of_prime_mul_dvd hp hpb
    simpa only [pow_succ, mul_assoc, mul_left_comm] using h

/-- Dividing an integral fraction by a prime remains integral when its displayed
denominator is not divisible by that prime. -/
theorem isIntegral_div_of_prime_mul {p a b : R} (hp : Prime p) (hpb : ¬p ∣ b)
    (h : IsIntegral R (algebraMap R K (p * a) / algebraMap R K b)) :
    IsIntegral R (algebraMap R K a / algebraMap R K b) := by
  have hb : b ≠ 0 := fun e => hpb (e ▸ dvd_zero p)
  obtain ⟨c, hc, hcn⟩ := (isIntegral_div_iff_exists_dvd K (p * a) b hb).mp h
  apply (isIntegral_div_iff_exists_dvd K a b hb).mpr
  refine ⟨c, hc, fun n => ?_⟩
  apply Prime.dvd_of_prime_pow_mul_dvd hp (fun hn => hpb (hp.dvd_of_dvd_pow hn)) n
  simpa only [mul_pow, mul_assoc, mul_left_comm] using hcn n

/-- The common multiplier for integral powers can be chosen outside any prime
parameter which does not divide the displayed denominator. -/
theorem exists_integral_power_multiplier_not_dvd {p a b : R}
    (hp : Prime p) (hpb : ¬p ∣ b)
    (h : IsIntegral R (algebraMap R K a / algebraMap R K b)) :
    ∃ c : R, ¬p ∣ c ∧ ∀ n : ℕ, b ^ n ∣ c * a ^ n := by
  have hb : b ≠ 0 := fun e => hpb (e ▸ dvd_zero p)
  obtain ⟨c, hc, hcn⟩ := (isIntegral_div_iff_exists_dvd K a b hb).mp h
  obtain ⟨k, d, hpd, rfl⟩ := WfDvdMonoid.max_power_factor' hc hp.not_isUnit
  refine ⟨d, hpd, fun n => ?_⟩
  apply Prime.dvd_of_prime_pow_mul_dvd hp (fun hn => hpb (hp.dvd_of_dvd_pow hn)) k
  simpa only [mul_assoc] using hcn n

/-- Reduce an integral fraction modulo a normal prime-parameter quotient. -/
theorem exists_sub_mul_dvd_parameter {p a b : R} (hp : Prime p) (hpb : ¬p ∣ b)
    [IsIntegrallyClosed (R ⧸ Ideal.span {p})]
    (h : IsIntegral R (algebraMap R K a / algebraMap R K b)) :
    ∃ r : R, p ∣ a - b * r := by
  let Q := R ⧸ Ideal.span {p}
  let q : R →+* Q := Ideal.Quotient.mk (Ideal.span {p})
  let : (Ideal.span {p}).IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  let : IsDomain Q := Ideal.Quotient.isDomain _
  have hbq : q b ≠ 0 := by
    intro hz
    exact hpb (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  obtain ⟨c, hpc, hcn⟩ := exists_integral_power_multiplier_not_dvd K hp hpb h
  have hcq : q c ≠ 0 := by
    intro hz
    exact hpc (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hbar : IsIntegral Q
      (algebraMap Q (FractionRing Q) (q a) / algebraMap Q (FractionRing Q) (q b)) := by
    apply (isIntegral_div_iff_exists_dvd (FractionRing Q) (q a) (q b) hbq).mpr
    refine ⟨q c, hcq, fun n => ?_⟩
    simpa only [map_mul, map_pow] using map_dvd q (hcn n)
  obtain ⟨r, hr⟩ := (isIntegrallyClosed_iff (FractionRing Q)).mp
    (inferInstance : IsIntegrallyClosed Q) hbar
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨s, Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp ?_)⟩
  change q (a - b * s) = 0
  rw [map_sub, map_mul, sub_eq_zero]
  apply IsFractionRing.injective Q (FractionRing Q)
  have hbF : algebraMap Q (FractionRing Q) (q b) ≠ 0 := by
    simpa using (IsFractionRing.injective Q (FractionRing Q)).ne hbq
  rw [eq_div_iff hbF] at hr
  simpa only [map_mul, mul_comm] using hr.symm

/-- Numerators over a fixed denominator that represent integral fractions. -/
def integralNumerators (b : R) : Ideal R where
  carrier := {a | IsIntegral R (algebraMap R K a / algebraMap R K b)}
  zero_mem' := by simpa using (isIntegral_zero : IsIntegral R (0 : K))
  add_mem' ha hc := by
    change IsIntegral R (_ / _)
    simpa only [map_add, add_div] using ha.add hc
  smul_mem' r a ha := by
    change IsIntegral R (algebraMap R K (r * a) / algebraMap R K b)
    simpa only [map_mul, mul_div_assoc] using (isIntegral_algebraMap (x := r)).mul ha

omit [IsDomain R] [IsNoetherianRing R] [IsFractionRing R K] in
@[simp] theorem mem_integralNumerators (b a : R) :
    a ∈ integralNumerators K b ↔ IsIntegral R (algebraMap R K a / algebraMap R K b) := Iff.rfl

/-- Normality of the prime-parameter quotient controls all integral fractions
whose displayed denominator is outside that parameter. -/
theorem dvd_of_isIntegral_div_of_normal_parameter [IsLocalRing R]
    {p a b : R} (hp : Prime p) (hpm : p ∈ IsLocalRing.maximalIdeal R) (hpb : ¬p ∣ b)
    [IsIntegrallyClosed (R ⧸ Ideal.span {p})]
    (h : IsIntegral R (algebraMap R K a / algebraMap R K b)) : b ∣ a := by
  have hb : b ≠ 0 := fun e => hpb (e ▸ dvd_zero p)
  have hbK : algebraMap R K b ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hb
  let I := integralNumerators K b
  have hI : I ≤ Ideal.span {b} := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot I.fg_of_isNoetherianRing
      (I := Ideal.span {p})
    · rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
      exact (Ideal.span_singleton_le_iff_mem _).mpr hpm
    · intro z hz
      obtain ⟨r, s, hs⟩ := exists_sub_mul_dvd_parameter K hp hpb hz
      have hsI : s ∈ I := by
        apply isIntegral_div_of_prime_mul K hp hpb
        have ht := hz.sub (isIntegral_algebraMap (x := r) (A := K))
        convert ht using 1
        rw [← hs, map_sub, map_mul]
        field_simp
      have he : z = b * r + p * s := by rw [← hs]; ring
      rw [he]
      exact Submodule.add_mem_sup (Ideal.mem_span_singleton.mpr ⟨r, rfl⟩)
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self p) hsI)
  exact Ideal.mem_span_singleton.mp (hI h)

end Fractions
end IsFractionRing
