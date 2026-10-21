/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.Ring

/-!
# Integral closure from localization away from a prime element

Prime lying-over in the actual integral closure supplies the one-denominator
cancellation step. Induction removes a power of the prime from the denominator.
The criterion requires no Noetherian, local, or dimension hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped nonZeroDivisors
universe u v

namespace Prime

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]

/-- An integral multiplier cannot introduce a new multiple of a prime in a
faithful domain extension. The prime of the actual integral closure is supplied
by native lying-over, without a finiteness hypothesis on the base ring. -/
theorem dvd_of_integral_mul {p a : R} (hp : Prime p) {z : S}
    (hz : IsIntegral R z) (ha : algebraMap R S a = algebraMap R S p * z) : p ∣ a := by
  let C := integralClosure R S
  let I : Ideal R := Ideal.span {p}
  let : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  have hi : Function.Injective (algebraMap R C) := by
    intro a b h
    apply FaithfulSMul.algebraMap_injective R S
    exact congrArg (fun x : C => (x : S)) h
  obtain ⟨Q, hQ, hQI⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := C) I (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hi]; exact bot_le)
  have hpQ : algebraMap R C p ∈ Q := by
    change p ∈ Q.under R
    rw [hQI]
    exact Ideal.mem_span_singleton_self p
  let zC : C := ⟨z, hz⟩
  have he : algebraMap R C a = algebraMap R C p * zC := by
    apply Subtype.ext
    exact ha
  apply Ideal.mem_span_singleton.mp
  change a ∈ I
  rw [← hQI]
  change algebraMap R C a ∈ Q
  rw [he]
  exact Q.mul_mem_right zC hpQ

/-- An integral element represented with a prime-power denominator already
comes from the original ring. -/
theorem exists_algebraMap_eq_of_integral_primePow_denominator
    {p : R} (hp : Prime p) {z : S} (hz : IsIntegral R z)
    (n : ℕ) (a : R) (ha : z * algebraMap R S p ^ n = algebraMap R S a) :
    ∃ b : R, algebraMap R S b = z := by
  have hpS : algebraMap R S p ≠ 0 := by
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective R S).ne hp.ne_zero
  induction n generalizing a with
  | zero => exact ⟨a, by simpa only [pow_zero, mul_one] using ha.symm⟩
  | succ n ih =>
    have hz' : IsIntegral R (z * algebraMap R S p ^ n) := by
      simpa only [map_pow] using hz.mul (isIntegral_algebraMap (x := p ^ n))
    have ha' : algebraMap R S a = algebraMap R S p * (z * algebraMap R S p ^ n) := by
      rw [← ha, pow_succ]
      ring
    obtain ⟨b, hb⟩ := hp.dvd_of_integral_mul hz' ha'
    apply ih b
    apply mul_left_cancel₀ hpS
    calc
      algebraMap R S p * (z * algebraMap R S p ^ n) =
          z * algebraMap R S p ^ (n + 1) := by rw [pow_succ]; ring
      _ = algebraMap R S a := ha
      _ = algebraMap R S p * algebraMap R S b := by rw [hb, map_mul]

end Prime

namespace IsIntegrallyClosedIn

variable {R : Type u} [CommRing R] [IsDomain R] {p : R}
variable (S : Type v) [CommRing S] [IsDomain S] [Algebra R S]
variable [IsLocalization.Away p S]

/-- A domain is integrally closed inside its localization away from a prime
element. This is a relative assertion and does not assume the localization is normal. -/
theorem of_isLocalizationAway_prime (hp : Prime p) : IsIntegrallyClosedIn R S := by
  have hi : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hp.ne_zero)
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hi
  refine isIntegrallyClosedIn_iff.mpr ⟨hi, ?_⟩
  intro z hz
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj p z
  exact hp.exists_algebraMap_eq_of_integral_primePow_denominator hz n a ha

end IsIntegrallyClosedIn

namespace IsIntegrallyClosed

variable {R : Type u} [CommRing R] [IsDomain R] {p : R}
variable (S : Type v) [CommRing S] [Algebra R S] [IsLocalization.Away p S]
variable [IsIntegrallyClosed S]

include S

/-- If localization away from a prime element is integrally closed, then the
original domain is integrally closed. No Noetherian hypothesis is used. -/
theorem of_isLocalizationAway_prime (hp : Prime p) : IsIntegrallyClosed R := by
  have hM := powers_le_nonZeroDivisors_of_noZeroDivisors hp.ne_zero
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  have hi : Function.Injective (algebraMap R S) := IsLocalization.injective S hM
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hi
  let : IsIntegrallyClosedIn R S := IsIntegrallyClosedIn.of_isLocalizationAway_prime S hp
  exact IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn (R := R) (S := S)

end IsIntegrallyClosed
