/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Minimal-prime contraction under supplied going down

Supporting original Grayson principal-face/local-length prerequisites for
`K2-018#prop:k2018-arithmetic-characters`
(`research/exposes/K2/018/expose.tex`), source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

Encoded conditional subset: for commutative A-algebras B, supplied
Algebra.HasGoingDown A B makes every minimal prime over the extension of an
ideal I contract to a minimal prime of I. For I prime it contracts exactly to
I. The normal-integral specialization retains IsIntegrallyClosed A, IsDomain
B, FaithfulSMul A B and Algebra.IsIntegral A B exactly as in its signature.
No flatness or Noetherian premise is introduced. The minimal-prime hypotheses
refer to the actual extended ideal, not an arbitrary target prime.

These generalized constructions support the original Grayson principal-face
component prerequisite. They do not assert a weighted filtration formula,
original-object face-cycle equality, or full motivic/arithmetic-character
comparison.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.GoingDownMinimalPrime` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`00b85bfbfdaa8be4265e0f346c5d67d8f9e29caaebe4d679e75c6359df9bd690`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Ideal
universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

theorem minimalPrime_map_under_of_goingDown [Algebra.HasGoingDown A B]
    (I : Ideal A) (q : Ideal B) (hq : q ∈ (I.map (algebraMap A B)).minimalPrimes) :
    q.under A ∈ I.minimalPrimes := by
  let : q.IsPrime := hq.isPrime
  refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mp hq.le⟩, ?_⟩
  intro p hp hpq
  let : p.IsPrime := hp.1
  obtain ⟨P, hPq, hPprime, hPover⟩ :=
    q.exists_ideal_le_liesOver_of_le (p := p) (q := q.under A) hpq
  have hIP : I.map (algebraMap A B) ≤ P := by
    apply Ideal.map_le_iff_le_comap.mpr
    change I ≤ P.under A
    rw [← hPover.over]
    exact hp.2
  have hqP : q ≤ P := hq.2 ⟨hPprime, hIP⟩ hPq
  have h := Ideal.comap_mono (f := algebraMap A B) hqP
  change q.under A ≤ P.under A at h
  rwa [← hPover.over] at h

/-- A minimal prime over the extension of a prime contracts to that prime under going down,
including integral extensions over a normal domain.

Source mapping: supporting generalized local construction for
`K2-018#prop:k2018-arithmetic-characters`, source snapshot
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Encoded prerequisite subset: supplied Algebra.HasGoingDown A B, a prime ideal I and q
minimal over its actual extension imply q.under A = I; no flatness or Noetherian premise
is used. -/
theorem minimalPrime_map_prime_under [Algebra.HasGoingDown A B]
    (I : Ideal A) [I.IsPrime] (q : Ideal B)
    (hq : q ∈ (I.map (algebraMap A B)).minimalPrimes) : q.under A = I := by
  have h := minimalPrime_map_under_of_goingDown I q hq
  rw [Ideal.minimalPrimes_eq_subsingleton_self] at h
  exact Set.mem_singleton_iff.mp h

theorem normal_integral_minimalPrime_contract [IsIntegrallyClosed A] [IsDomain B]
    [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (I : Ideal A) [I.IsPrime] (q : Ideal B)
    (hq : q ∈ (I.map (algebraMap A B)).minimalPrimes) : q.under A = I :=
  minimalPrime_map_prime_under I q hq

end Ideal
