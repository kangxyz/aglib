/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.HeightOne
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Associated primes of principal quotients in normal local domains

The local associated-prime obstruction is converted into a fraction multiplying the maximal
ideal into the ring. Normality then bounds the height of that maximal ideal by one.
-/

@[expose] public section

noncomputable section

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsLocalRing R] [IsIntegrallyClosed R]

/-- The maximal ideal of a normal Noetherian local domain can be associated to a nonzero
principal quotient only in dimension at most one. -/
theorem maximalIdeal_height_le_one_of_associated_principal {b : R} (hb : b ≠ 0)
    (h : IsAssociatedPrime (maximalIdeal R) (R ⧸ Ideal.span {b})) :
    (maximalIdeal R).height ≤ 1 := by
  obtain ⟨_, c, hc⟩ := isAssociatedPrime_iff.mp h
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  have ha : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
    intro hz
    have htop : maximalIdeal R = ⊤ := by
      simpa only [hz, Submodule.colon_singleton_zero] using hc
    exact (maximalIdeal.isMaximal R).ne_top htop
  let K := FractionRing R
  have hbK : algebraMap R K b ≠ 0 := by
    simpa using (IsFractionRing.injective R K).ne hb
  apply maximalIdeal_height_le_one_of_fraction K
    (algebraMap R K a / algebraMap R K b)
  · rintro ⟨t, ht⟩
    apply ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨t, (IsFractionRing.injective R K) ?_⟩
    have he := (eq_div_iff hbK).mp ht
    simpa only [map_mul, mul_comm] using he.symm
  · intro r hr
    have hrzero : r • Ideal.Quotient.mk (Ideal.span {b}) a = 0 := by
      have hr' : r ∈ (⊥ : Submodule R (R ⧸ Ideal.span {b})).colon
          {Ideal.Quotient.mk (Ideal.span {b}) a} := hc ▸ hr
      simpa only [Submodule.mem_bot] using (Submodule.mem_colon_singleton.mp hr')
    have hrdiv : b ∣ r * a := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul] using hrzero
    obtain ⟨k, hk⟩ := hrdiv
    refine ⟨k, ?_⟩
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hbK).mpr
    simpa only [map_mul, mul_comm] using (congrArg (algebraMap R K) hk).symm

end IsLocalRing
