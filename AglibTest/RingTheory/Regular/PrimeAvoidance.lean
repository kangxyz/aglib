/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Regular.PrimeAvoidance

/-! Focused consumer of the avoidance of associated primes by a vector of linear forms. -/

@[expose] public section

/-- One linear form, regular on one finite module. -/
example {k V A M : Type} [Field k] [Infinite k] [AddCommGroup V] [Module k V] [CommRing A]
    [IsNoetherianRing A] [Algebra k A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (lam : V →ₗ[k] A) (h : ∀ P ∈ associatedPrimes A M, ∃ v, lam v ∉ P) :
    ∃ v : V, IsSMulRegular M (lam v) := by
  obtain ⟨v, hv⟩ := associatedPrimes.exists_forall_isSMulRegular (J := Unit) (fun _ => A)
    (fun _ => M) (fun _ => lam) (fun _ => h)
  exact ⟨v, hv ()⟩

/--
info: 'associatedPrimes.exists_forall_isSMulRegular'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms associatedPrimes.exists_forall_isSMulRegular
