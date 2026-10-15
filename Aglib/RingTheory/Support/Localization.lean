/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.IteratedModuleLength
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Support at a localized minimal prime

For a finite module, minimal support primes after localization correspond to its original
minimal support primes contained in the localization prime. The equivalence uses canonical
extension and contraction; no annihilator base-change equality is supplied as a premise.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.LocalizedMinimalSupport` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`c90ea23ec2031a113bd73f186233dae0e4d63466fdeb6ee64d0a6dbd391bdcdd`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open scoped _root_.TensorProduct
namespace Module
universe u v
variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

theorem _root_.Ideal.minimalPrimes_eq_of_prime_le_iff (I J : Ideal A)
    (h : ∀ p : Ideal A, p.IsPrime → (I ≤ p ↔ J ≤ p)) : I.minimalPrimes = J.minimalPrimes := by
  ext p
  constructor
  · intro hp
    refine ⟨⟨hp.isPrime, (h p hp.isPrime).mp hp.le⟩, ?_⟩
    intro q hq hqp
    exact hp.2 ⟨hq.1, (h q hq.1).mpr hq.2⟩ hqp
  · intro hp
    refine ⟨⟨hp.isPrime, (h p hp.isPrime).mpr hp.le⟩, ?_⟩
    intro q hq hqp
    exact hp.2 ⟨hq.1, (h q hq.1).mp hq.2⟩ hqp

theorem annihilator_le_localized_iff [Module.Finite A M] (Q : Ideal A) [Q.IsPrime]
    (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] :
    Module.annihilator (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[A] M) ≤ p ↔
      Module.annihilator A M ≤ p.under A := by
  simpa only [Module.mem_support_iff_of_finite] using mem_support_localized_iff (M := M) Q p

/-- The intrinsic minimal primes of the localized original module correspond
to the original minimal support primes. No annihilator base-change equality
is supplied or assumed in this argument. -/
theorem localized_minimalSupport_iff [Module.Finite A M] (Q : Ideal A) [Q.IsPrime]
    (p : Ideal (Localization.AtPrime Q)) :
    p ∈ (Module.annihilator (Localization.AtPrime Q)
      (Localization.AtPrime Q ⊗[A] M)).minimalPrimes ↔
      p.under A ∈ (Module.annihilator A M).minimalPrimes := by
  have he := Ideal.minimalPrimes_eq_of_prime_le_iff
    (Module.annihilator (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[A] M))
    ((Module.annihilator A M).map (algebraMap A (Localization.AtPrime Q))) (by
      intro r hr
      let := hr
      rw [Ideal.map_le_iff_le_comap]
      exact annihilator_le_localized_iff (M := M) Q r)
  rw [he, IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q)]
  rfl

/-- Extension and contraction identify the minimal primes of the localized module's
annihilator with the minimal primes of the original annihilator lying below `Q`.
Finite generation of the original module supplies the support comparison. -/
def localizedMinimalSupportEquiv [Module.Finite A M] (Q : Ideal A) [Q.IsPrime] :
    {p : Ideal (Localization.AtPrime Q) //
      (Module.annihilator (Localization.AtPrime Q)
        (Localization.AtPrime Q ⊗[A] M)).IsMinimalPrime p} ≃
    {P : Ideal A // (Module.annihilator A M).IsMinimalPrime P ∧ P ≤ Q} where
  toFun p :=
    haveI := p.property.isPrime
    ⟨p.val.under A, (localized_minimalSupport_iff Q p.val).mp p.property,
      ((IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime Q) Q)
        ⟨p.val, p.property.isPrime⟩).2.2⟩
  invFun P :=
    have := P.property.1.isPrime
    haveI : (P.val.map (algebraMap A (Localization.AtPrime Q))).IsPrime :=
      Ideal.isPrime_map_of_isLocalizationAtPrime Q P.property.2
    ⟨P.val.map (algebraMap A (Localization.AtPrime Q)),
      (localized_minimalSupport_iff Q _).mpr (by
        rw [Ideal.under_map_of_isLocalizationAtPrime Q P.property.2]
        exact P.property.1)⟩
  left_inv p := by
    apply Subtype.ext
    exact IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) p.val
  right_inv P := by
    have := P.property.1.isPrime
    apply Subtype.ext
    exact Ideal.under_map_of_isLocalizationAtPrime Q P.property.2

@[simp] theorem localizedMinimalSupportEquiv_apply_val [Module.Finite A M]
    (Q : Ideal A) [Q.IsPrime]
    (p : {p : Ideal (Localization.AtPrime Q) //
      (Module.annihilator (Localization.AtPrime Q)
        (Localization.AtPrime Q ⊗[A] M)).IsMinimalPrime p}) :
    (localizedMinimalSupportEquiv (M := M) Q p).val = p.val.under A := rfl

@[simp] theorem localizedMinimalSupportEquiv_symm_apply_val [Module.Finite A M]
    (Q : Ideal A) [Q.IsPrime]
    (P : {P : Ideal A // (Module.annihilator A M).IsMinimalPrime P ∧ P ≤ Q}) :
    ((localizedMinimalSupportEquiv (M := M) Q).symm P).val =
      P.val.map (algebraMap A (Localization.AtPrime Q)) := rfl

end Module
