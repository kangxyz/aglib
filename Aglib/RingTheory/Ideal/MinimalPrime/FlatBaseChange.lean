/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.RingTheory.Localization.LengthFlatBaseChange
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!+# Minimal support primes under flat scalar extension

Prerequisite for K2-018#prop:k2018-arithmetic-characters, source revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982. This only treats contraction and
partition of minimal primes of an extended ideal; it does not encode the
Grayson finite-comparison assertion.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.MinimalFlatBaseChange` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`b2bd805d2fc33379b16390bd5c7ea09670e8b7a675b882c9039c568e81bf6177`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Ideal
universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Flatness forces a minimal prime of an extended ideal to contract to a
minimal prime of the original ideal. No Noetherian or domain assumption. -/
theorem minimalPrime_map_under [Module.Flat A B] (I : Ideal A)
    (q : Ideal B) (hq : q ∈ (I.map (algebraMap A B)).minimalPrimes) :
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

/-- Minimal primes of an extended ideal partition into the minimal primes of
the extensions of their contracted minimal primes. This is a literal ideal
statement, including the empty support of the unit ideal. -/
theorem minimalPrime_map_iff [Module.Flat A B] (I : Ideal A)
    (q : Ideal B) [q.IsPrime] :
    q ∈ (I.map (algebraMap A B)).minimalPrimes ↔
      q.under A ∈ I.minimalPrimes ∧
      q ∈ ((q.under A).map (algebraMap A B)).minimalPrimes := by
  constructor
  · intro hq
    have hp := minimalPrime_map_under I q hq
    refine ⟨hp, ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mpr le_rfl⟩, ?_⟩⟩
    intro P hP hPq
    exact hq.2 ⟨hP.1, (Ideal.map_mono hp.le).trans hP.2⟩ hPq
  · rintro ⟨hp, hq⟩
    refine ⟨⟨inferInstance,
      (Ideal.map_mono hp.le).trans (Ideal.map_le_iff_le_comap.mpr le_rfl)⟩, ?_⟩
    intro P hP hPq
    let : P.IsPrime := hP.1
    have hpP : q.under A ≤ P.under A :=
      hp.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.mp hP.2⟩
        (Ideal.comap_mono hPq)
    exact hq.2 ⟨hP.1, Ideal.map_le_iff_le_comap.mpr hpP⟩ hPq

end Ideal
