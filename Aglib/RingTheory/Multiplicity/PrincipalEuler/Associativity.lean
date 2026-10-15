/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PrimeFiltration.Multiplicity
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Support
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Weighted principal Euler associativity

Supporting auxiliary for `K2-018#prop:k2018-arithmetic-characters`
(`research/exposes/K2/018/expose.tex`), source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

For a finite module over a Noetherian local ring, finite M/tM and t in the maximal ideal derive
the support-dimension bound and Euler associativity. Regularity on M derives the
principal-cokernel weighted formula.

This module supplies the stated local algebraic construction; it does not
claim a full original face-cycle or motivic comparison theorem.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.PrincipalEulerAssociativity` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`bf1fac16ef81cd1e488dd55b90c1a3ebb8edcd9faa70f6691fe1b5843db48f74`.
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

theorem supportDim_nonpos_of_length_ne_top (hM : Module.length A M ≠ ⊤) :
    Module.supportDim A M ≤ 0 := by
  apply Order.krullDim_nonpos_iff_forall_isMax.mpr
  intro p q hpq
  have hm := isMaximal_of_mem_support_of_length_ne_top hM p.val p.property
  have he := hm.eq_of_le q.val.isPrime.ne_top hpq
  exact he.symm.le

/-- Finite M/tM and t in the local maximal ideal imply dimension at most one
for the support of the actual original module. No equidimensionality or
Cohen--Macaulay premise is supplied. -/
theorem supportDim_le_one_of_finite_cokernel [IsNoetherianRing A] [IsLocalRing A]
    [Module.Finite A M] (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hM : Module.length A (ScalarCokernel M t) ≠ ⊤) : Module.supportDim A M ≤ 1 := by
  have hd : Module.supportDim A (QuotSMulTop t M) ≤ 0 := by
    have he : Module.support A (QuotSMulTop t M) =
        Module.support A (ScalarCokernel M t) := by
      rw [Module.support_quotSMulTop, support_scalarCokernel]
    rw [Module.supportDim, he]
    exact supportDim_nonpos_of_length_ne_top hM
  have h := (Module.supportDim_le_supportDim_quotSMulTop_succ (M := M) ht).trans
    (add_le_add hd (le_refl 1))
  simpa only [zero_add] using h

/-- In dimension at most one, a support prime is either minimal in the
original support or the local maximal ideal. -/
theorem support_prime_minimal_or_maximal [IsLocalRing A] [Module.Finite A M]
    (hd : Module.supportDim A M ≤ 1) (p : PrimeSpectrum A) (hp : p ∈ Module.support A M) :
    p.asIdeal ∈ (Module.annihilator A M).minimalPrimes ∨
      p.asIdeal = IsLocalRing.maximalIdeal A := by
  have hh := Order.krullDim_le_one_iff.mp hd (⟨p, hp⟩ : Module.support A M)
  rcases hh with hmin | hmax
  · left
    refine ⟨⟨p.isPrime, Module.annihilator_le_of_mem_support hp⟩, ?_⟩
    intro q hq hqp
    let q' : PrimeSpectrum A := ⟨q, hq.1⟩
    have hqs : q' ∈ Module.support A M := Module.mem_support_iff_of_finite.mpr hq.2
    exact hmin (show (⟨q', hqs⟩ : Module.support A M) ≤ ⟨p, hp⟩ from hqp)
  · right
    let m : PrimeSpectrum A := ⟨IsLocalRing.maximalIdeal A, inferInstance⟩
    have hpm : p ≤ m := IsLocalRing.le_maximalIdeal p.isPrime.ne_top
    have hms : m ∈ Module.support A M := Module.mem_support_mono hpm hp
    exact congrArg PrimeSpectrum.asIdeal
      (hpm.antisymm (hmax (show (⟨p, hp⟩ : Module.support A M) ≤ ⟨m, hms⟩ from hpm)))

theorem scalar_regular_primeQuotient (p : Ideal A) [p.IsPrime] (t : A) (ht : t ∉ p) :
    IsSMulRegular (A ⧸ p) t := by
  intro x y hxy
  have htn : (Ideal.Quotient.mk p t) ≠ 0 := Ideal.Quotient.eq_zero_iff_mem.not.mpr ht
  exact mul_left_cancel₀ htn hxy

/-- A term is retained exactly at minimal primes of the original module.
Its weight is the literal localized original-module length. -/
def minimalPrimeEulerTerm (M : Type v) [AddCommGroup M] [Module A M]
    (t : A) (p : Ideal A) : ℤ := by
  classical
  exact if hp : p ∈ (Module.annihilator A M).minimalPrimes then
    letI := hp.isPrime
    ((Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[A] M)).toNat : ℤ) * principalEuler (N := A ⧸ p) t
  else 0

namespace PrimeFiltrationFrom

/-- The weighted local Euler formula has actual localized original lengths
as coefficients. The only geometric premise here is a support-dimension
bound; the next corollary derives it from finite M/tM and t in the maximal ideal. -/
theorem principalEuler_eq_weighted_sum_of_supportDim [IsNoetherianRing A] [IsLocalRing A]
    [Module.Finite A M] (D : PrimeFiltrationFrom M ⊥) (t : A)
    (hd : Module.supportDim A M ≤ 1)
    (hM : Module.length A (ScalarCokernel M t) ≠ ⊤) :
    principalEuler (N := M) t = ∑ p ∈ D.primes.toFinset,
      minimalPrimeEulerTerm (M := M) t p := by
  classical
  rw [D.principalEuler_eq_sum_of_finite_cokernel t hM,
    Finset.sum_list_map_count]
  apply Finset.sum_congr rfl
  intro p hp
  have hpl : p ∈ D.primes := List.mem_toFinset.mp hp
  by_cases hmin : p ∈ (Module.annihilator A M).minimalPrimes
  · let := hmin.isPrime
    have he := D.localized_length_eq_count_of_bot p hmin
    simp only [minimalPrimeEulerTerm, dite_eq_left hmin, he, ENat.toNat_natCast,
      nsmul_eq_mul]
  · have hmax : p = IsLocalRing.maximalIdeal A :=
      (support_prime_minimal_or_maximal hd ⟨p, D.primes_isPrime p hpl⟩
        (D.prime_mem_support p hpl)).resolve_left hmin
    have : p.IsMaximal := hmax ▸ inferInstance
    have : IsSimpleModule A (A ⧸ p) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨p, inferInstance, ⟨LinearEquiv.refl A _⟩⟩
    have hz : principalEuler (N := A ⧸ p) t = 0 :=
      principalEuler_zero_of_finite_length t (by simp)
    simp only [hz, smul_zero, minimalPrimeEulerTerm, dite_eq_right hmin]

theorem principalEuler_eq_weighted_sum [IsNoetherianRing A] [IsLocalRing A]
    [Module.Finite A M] (D : PrimeFiltrationFrom M ⊥) (t : A)
    (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hM : Module.length A (ScalarCokernel M t) ≠ ⊤) :
    principalEuler (N := M) t = ∑ p ∈ D.primes.toFinset,
      minimalPrimeEulerTerm (M := M) t p :=
  D.principalEuler_eq_weighted_sum_of_supportDim t
    (supportDim_le_one_of_finite_cokernel t ht hM) hM

end PrimeFiltrationFrom

/-- The finite set of minimal primes of the original finite module. -/
def moduleMinimalPrimes [IsNoetherianRing A] (M : Type v) [AddCommGroup M] [Module A M] :
    Finset (Ideal A) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing A (Module.annihilator A M)).toFinset

@[simp] theorem mem_moduleMinimalPrimes [IsNoetherianRing A] (p : Ideal A) :
    p ∈ moduleMinimalPrimes (A := A) M ↔
      p ∈ (Module.annihilator A M).minimalPrimes := Set.Finite.mem_toFinset _

/-- Euler associativity over the intrinsic minimal support primes. The
finite filtration is constructed internally and is absent from the conclusion. -/
theorem principalEuler_associativity [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A M]
    (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hM : Module.length A (ScalarCokernel M t) ≠ ⊤) :
    principalEuler (N := M) t = ∑ p ∈ moduleMinimalPrimes (A := A) M,
      minimalPrimeEulerTerm M t p := by
  classical
  obtain ⟨D⟩ := nonempty_primeFiltration (A := A) M
  rw [D.principalEuler_eq_weighted_sum t ht hM]
  have hsub : moduleMinimalPrimes (A := A) M ⊆ D.primes.toFinset := by
    intro p hp
    exact List.mem_toFinset.mpr (D.minimalPrime_mem_primes p (mem_moduleMinimalPrimes p |>.mp hp))
  apply (Finset.sum_subset hsub ?_).symm
  intro p _ hp
  have hmin : p ∉ (Module.annihilator A M).minimalPrimes :=
    fun hh => hp (mem_moduleMinimalPrimes p |>.mpr hh)
  simp only [minimalPrimeEulerTerm, dite_eq_right hmin]

/-- The product of the `toNat` lengths of `M` localized at `p` and the `t`-cokernel of `A ⧸ p`,
viewed in `ℤ`; it is zero unless `p` is minimal over the annihilator of `M`. -/
def minimalPrimeCokernelTerm (M : Type v) [AddCommGroup M] [Module A M]
    (t : A) (p : Ideal A) : ℤ := by
  classical
  exact if hp : p ∈ (Module.annihilator A M).minimalPrimes then
    letI := hp.isPrime
    ((Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[A] M)).toNat : ℤ) *
        ((Module.length A (ScalarCokernel (A ⧸ p) t)).toNat : ℤ)
  else 0

theorem minimalPrimeEulerTerm_eq_cokernelTerm (t : A) (hr : IsSMulRegular M t) (p : Ideal A) :
    minimalPrimeEulerTerm M t p = minimalPrimeCokernelTerm M t p := by
  classical
  by_cases hp : p ∈ (Module.annihilator A M).minimalPrimes
  · let := hp.isPrime
    have ht : t ∉ p := hr.notMem_of_mem_minimalPrimes hp
    simp only [minimalPrimeEulerTerm, minimalPrimeCokernelTerm, dite_eq_left hp]
    rw [principalEuler_of_regular t (scalar_regular_primeQuotient p t ht)]
  · simp only [minimalPrimeEulerTerm, minimalPrimeCokernelTerm, dite_eq_right hp]

/-- Weighted principal associativity for the original module. The length
weights are localized original lengths, and regularity of t on M derives
regularity on the contributing prime factors. All scalar homology finiteness
and the dimension-one support condition are proved above from hM. -/
theorem principalCokernel_associativity [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A M]
    (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A) (hr : IsSMulRegular M t)
    (hM : Module.length A (ScalarCokernel M t) ≠ ⊤) :
    ((Module.length A (ScalarCokernel M t)).toNat : ℤ) =
      ∑ p ∈ moduleMinimalPrimes (A := A) M, minimalPrimeCokernelTerm M t p := by
  rw [← principalEuler_of_regular t hr, principalEuler_associativity t ht hM]
  exact Finset.sum_congr rfl fun p _ => minimalPrimeEulerTerm_eq_cokernelTerm t hr p

/-- Every contributing minimal-prime factor has finite scalar homology,
including finite principal quotient length. -/
theorem finitePrincipal_minimalPrime [IsNoetherianRing A] [Module.Finite A M]
    (t : A) (hM : Module.length A (ScalarCokernel M t) ≠ ⊤) (p : Ideal A)
    (hp : p ∈ (Module.annihilator A M).minimalPrimes) : FinitePrincipal (A ⧸ p) t := by
  apply finitePrincipal_of_support_subset t hM
  intro q hq
  apply Module.mem_support_iff_of_finite.mpr
  have hle : p ≤ q.asIdeal := by
    simpa only [Ideal.annihilator_quotient] using Module.annihilator_le_of_mem_support hq
  exact hp.le.trans hle

end Module
