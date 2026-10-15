/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.RingTheory.PrimeFiltration.Support
public import Aglib.RingTheory.PrimeFiltration.Length
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Actual prime-filtration multiplicities

Supporting auxiliary for `K2-018#prop:k2018-arithmetic-characters`
(`research/exposes/K2/018/expose.tex`), source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

Localizing the literal filtration identifies minimal-prime occurrence counts with localized
lengths of the original module.

This module supplies the stated local algebraic construction; it does not
claim a full original face-cycle or motivic comparison theorem.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.PrimeFiltrationMultiplicity` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`0f5acb5ba60a99f298e2f85fe90763dcc7f3366b82dca8eb5b5c7bb8dd0ff019`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped _root_.TensorProduct
namespace Module
open _root_.TensorProduct
universe u v w
variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
variable (B : Type w) [CommRing B] [Algebra A B]

theorem length_baseChange_add_of_submodule_le [Module.Flat A B]
    (U V : Submodule A M) (hUV : U ≤ V) :
    Module.length B (B ⊗[A] V) = Module.length B (B ⊗[A] U) +
      Module.length B (B ⊗[A] (V ⧸ U.comap V.subtype)) := by
  let C : Submodule A V := U.comap V.subtype
  let f : U →ₗ[A] V := Submodule.inclusion hUV
  have hex : Function.Exact f C.mkQ := by
    intro x
    constructor
    · intro hx
      have hm : (x : M) ∈ U := (Submodule.Quotient.mk_eq_zero C).mp hx
      exact ⟨⟨x, hm⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero C).mpr
      exact y.property
  exact Module.length_eq_add_of_exact
    (AlgebraTensorModule.lTensor B B f) (AlgebraTensorModule.lTensor B B C.mkQ)
    (by simpa using (Module.Flat.lTensor_preserves_injective_linearMap (M := B) f
      (Submodule.inclusion_injective hUV)))
    (by simpa using LinearMap.lTensor_surjective B (Submodule.mkQ_surjective C))
    (by simpa using Module.Flat.lTensor_exact (M := B) hex)

namespace PrimeFiltrationFrom

/-- Localizing a literal prime filtration computes length, before any finite
length or multiplicity assertion is made. -/
theorem length_baseChange_eq_add_sum [Module.Flat A B]
    {U : Submodule A M} (D : PrimeFiltrationFrom M U) :
    Module.length B (B ⊗[A] M) = Module.length B (B ⊗[A] U) +
      (D.primes.map fun p => Module.length B (B ⊗[A] (A ⧸ p))).sum := by
  induction D with
  | top =>
    simpa only [primes, List.map_nil, List.sum_nil, add_zero] using
      (AlgebraTensorModule.congr (LinearEquiv.refl B B)
        (Submodule.topEquiv (R := A) (M := M))).length_eq.symm
  | @step U V hUV p hp e tail ih =>
    have hstep := length_baseChange_add_of_submodule_le B U V hUV.le
    rw [(AlgebraTensorModule.congr (LinearEquiv.refl B B) e).length_eq] at hstep
    rw [hstep] at ih
    simpa only [primes, List.map_cons, List.sum_cons, add_assoc] using ih

end PrimeFiltrationFrom

variable {B}

/-- At p, the literal factor A/q has length one when q=p, and vanishes
when q is not contained in p. -/
theorem localized_primeQuotient_length (p q : Ideal A) [p.IsPrime]
    (hq : q ≤ p → q = p) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[A] (A ⧸ q)) = if q = p then 1 else 0 := by
  classical
  let C := Localization.AtPrime p
  rw [← (Ideal.qoutMapEquivTensorQout (I := q) C).length_eq]
  by_cases hqp : q = p
  · subst q
    rw [ite_eq_left rfl, IsLocalization.AtPrime.map_eq_maximalIdeal]
    have : IsSimpleModule C (C ⧸ IsLocalRing.maximalIdeal C) := by
      exact isSimpleModule_iff_quot_maximal.mpr
        ⟨IsLocalRing.maximalIdeal C, inferInstance, ⟨LinearEquiv.refl C _⟩⟩
    exact Module.length_eq_one C _
  · rw [ite_eq_right hqp, IsLocalization.AtPrime.map_eq_top_of_not_le C (fun h => hqp (hq h))]
    exact Module.length_eq_zero

namespace PrimeFiltrationFrom

/-- The occurrence multiplicity of a minimal prime in an actual filtration
equals the local length of the original module. The proof localizes the
literal exact sequences; it does not assume this equality as a certificate. -/
theorem localized_length_eq_count {U : Submodule A M} (D : PrimeFiltrationFrom M U)
    (p : Ideal A) [p.IsPrime] (hp : p ∈ (Module.annihilator A M).minimalPrimes) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] M) =
      Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] U) +
        (D.primes.count p : ℕ∞) := by
  classical
  rw [D.length_baseChange_eq_add_sum (Localization.AtPrime p)]
  congr 1
  have hfac : ∀ q ∈ D.primes,
      Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] (A ⧸ q)) =
        if q = p then 1 else 0 := by
    intro q hq
    apply localized_primeQuotient_length p q
    intro hqp
    have ha : Module.annihilator A M ≤ q :=
      Module.annihilator_le_of_mem_support (D.prime_mem_support q hq)
    exact hqp.antisymm (hp.2 ⟨D.primes_isPrime q hq, ha⟩ hqp)
  have aux : ∀ ps : List (Ideal A),
      (∀ q ∈ ps,
        Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] (A ⧸ q)) =
          if q = p then 1 else 0) →
      (ps.map fun q => Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⊗[A] (A ⧸ q))).sum = (ps.count p : ℕ∞) := by
    intro ps
    induction ps with
    | nil => intro _; simp
    | cons q ps ih =>
      intro hh
      have hq := hh q (by simp)
      have hs := ih (fun r hr => hh r (List.mem_cons_of_mem q hr))
      by_cases hqp : q = p
      · subst q
        simp [List.map_cons, List.sum_cons, hq, hs, add_comm]
      · simp [List.map_cons, List.sum_cons, hq, hs, hqp]
  exact aux D.primes hfac

theorem localized_length_eq_count_of_bot (D : PrimeFiltrationFrom M ⊥)
    (p : Ideal A) [p.IsPrime] (hp : p ∈ (Module.annihilator A M).minimalPrimes) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] M) =
      (D.primes.count p : ℕ∞) := by
  have he := D.localized_length_eq_count p hp
  have hz : Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[A] (⊥ : Submodule A M)) = 0 := Module.length_eq_zero
  simpa only [hz, zero_add] using he

theorem exists_prime_le_of_mem_support {U : Submodule A M} (D : PrimeFiltrationFrom M U)
    (p : PrimeSpectrum A) (hp : p ∈ Module.support A M)
    (hU : p ∉ Module.support A U) : ∃ q ∈ D.primes, q ≤ p.asIdeal := by
  induction D with
  | top =>
    exact (hU (by rw [(Submodule.topEquiv (R := A) (M := M)).support_eq]; exact hp)).elim
  | @step U V hUV q hq e tail ih =>
    by_cases hV : p ∈ Module.support A V
    · let C : Submodule A V := U.comap V.subtype
      let f : U →ₗ[A] V := Submodule.inclusion hUV.le
      have hex : Function.Exact f C.mkQ := by
        apply LinearMap.exact_iff.mpr
        simp only [f, C, Submodule.range_inclusion, Submodule.ker_mkQ]
      rw [Module.support_of_exact hex (Submodule.inclusion_injective hUV.le)
        (Submodule.mkQ_surjective C)] at hV
      have hC := hV.resolve_left hU
      rw [e.support_eq] at hC
      have hle : q ≤ p.asIdeal := by
        simpa only [Ideal.annihilator_quotient] using Module.annihilator_le_of_mem_support hC
      exact ⟨q, by simp [primes], hle⟩
    · obtain ⟨r, hr, hrp⟩ := ih hV
      exact ⟨r, List.mem_cons_of_mem q hr, hrp⟩

/-- The distinct minimal support primes are exactly the minimal primes
occurring in any complete actual prime filtration. -/
theorem minimalPrime_mem_primes [Module.Finite A M] (D : PrimeFiltrationFrom M ⊥)
    (p : Ideal A) (hp : p ∈ (Module.annihilator A M).minimalPrimes) : p ∈ D.primes := by
  let p' : PrimeSpectrum A := ⟨p, hp.isPrime⟩
  have hps : p' ∈ Module.support A M := Module.mem_support_iff_of_finite.mpr hp.le
  obtain ⟨q, hq, hqp⟩ := D.exists_prime_le_of_mem_support p' hps (by simp [Module.support_eq_empty])
  have ha : Module.annihilator A M ≤ q :=
    Module.annihilator_le_of_mem_support (D.prime_mem_support q hq)
  have he : q = p := hqp.antisymm (hp.2 ⟨D.primes_isPrime q hq, ha⟩ hqp)
  exact he ▸ hq

end PrimeFiltrationFrom
end Module
