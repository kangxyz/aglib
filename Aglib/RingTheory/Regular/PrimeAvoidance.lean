/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Avoiding associated primes with a vector of linear forms

Let `k` be an infinite field and `V` a `k`-vector space. For each `j` in a finite index type let
`λⱼ : V → Aⱼ` be a `k`-linear map into a Noetherian `k`-algebra and `Mⱼ` a finitely generated
`Aⱼ`-module. If no associated prime of any `Mⱼ` contains `λⱼ V`, then one vector `v` makes every
`λⱼ v` a nonzerodivisor on `Mⱼ` (`associatedPrimes.exists_forall_isSMulRegular`). The proof
uses the finiteness of associated primes (`associatedPrimes.finite`, Stacks 00LC), the
description of zero divisors as their union (`biUnion_associatedPrimes_eq_compl_regular`) and the
fact that a vector space over an infinite field is not a finite union of proper subspaces
(`Submodule.exists_forall_notMem_of_forall_ne_top`).

This is the commutative algebra of a general hyperplane (Nitsure, arXiv:math/0504590v1, p. 10):
on projective space, `V = Γ(O(1))`, the `Aⱼ` are the coordinate charts and `λⱼ h = h / Xⱼ`.
-/

@[expose] public section

namespace associatedPrimes

/-- **Avoiding associated primes**: over an infinite field, one vector `v` makes every `λⱼ v` a
nonzerodivisor on `Mⱼ`, provided no associated prime of any `Mⱼ` contains `λⱼ V`. -/
theorem exists_forall_isSMulRegular {k V : Type*} [Field k] [Infinite k] [AddCommGroup V]
    [Module k V] {J : Type*} [Finite J] (A : J → Type*) [∀ j, CommRing (A j)]
    [∀ j, IsNoetherianRing (A j)] [∀ j, Algebra k (A j)] (M : J → Type*)
    [∀ j, AddCommGroup (M j)] [∀ j, Module (A j) (M j)] [∀ j, Module.Finite (A j) (M j)]
    (lam : ∀ j, V →ₗ[k] A j)
    (h : ∀ j, ∀ P ∈ associatedPrimes (A j) (M j), ∃ v, lam j v ∉ P) :
    ∃ v : V, ∀ j, IsSMulRegular (M j) (lam j v) := by
  classical
  let ι := Σ j, associatedPrimes (A j) (M j)
  have : ∀ j, Finite (associatedPrimes (A j) (M j)) := fun j =>
    (associatedPrimes.finite (A j) (M j)).to_subtype
  have : Finite ι := inferInstance
  let p : ι → Submodule k V := fun i =>
    (i.2.1.restrictScalars k).comap (lam i.1)
  have hp (i : ι) : p i ≠ ⊤ := by
    intro htop
    obtain ⟨v, hv⟩ := h i.1 i.2.1 i.2.2
    have hmem : v ∈ p i := by
      rw [htop]
      trivial
    exact hv hmem
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨v, fun j => ?_⟩
  by_contra hreg
  have hmem : lam j v ∈ ⋃ P ∈ associatedPrimes (A j) (M j), (P : Set (A j)) := by
    rw [biUnion_associatedPrimes_eq_compl_regular (A j) (M j)]
    exact hreg
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hmem
  obtain ⟨P, hP, hvP⟩ := hmem
  exact hv ⟨j, ⟨P, hP⟩⟩ hvP

end associatedPrimes
