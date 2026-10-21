/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-!
# Transporting the canonical summand equation through linear equivalences
-/

@[expose] public section

noncomputable section

universe u v wA wB wC wD wE

namespace DirectSum

variable {R : Type u} [Semiring R] {ι : Type v} [DecidableEq ι]
  {A : ι → Type wA} [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
  {B : ι → Type wB} [∀ i, AddCommMonoid (B i)] [∀ i, Module R (B i)]
  {C : Type wC} [AddCommMonoid C] [Module R C]
  {D : Type wD} [AddCommMonoid D] [Module R D]
  {E : Type wE} [AddCommMonoid E] [Module R E]

/-- The common constructor for a direct-sum comparison transported through three
linear equivalences. Keeping this constructor shared also keeps its module presentations shared. -/
def transportEquiv (eᵢ : ∀ i, B i ≃ₗ[R] A i) (s : C ≃ₗ[R] ⨁ i, B i)
    (t : C ≃ₗ[R] D) (e : D ≃ₗ[R] E) : (⨁ i, A i) ≃ₗ[R] E :=
  (congrLinearEquiv (fun i => (eᵢ i).symm)).trans (s.symm.trans (t.trans e))

/-- A computed direct-sum equivalence is canonical when its two constituent
comparisons preserve the specified summand maps. All module universes are independent. -/
theorem congrLinearEquiv_trans_apply_lof
    (eᵢ : ∀ i, B i ≃ₗ[R] A i) (s : C ≃ₗ[R] ⨁ i, B i)
    (t : C ≃ₗ[R] D) (e : D ≃ₗ[R] E)
    (j : ∀ i, B i →ₗ[R] C) (f : ∀ i, A i →ₗ[R] E)
    (hs : ∀ i y, s (j i y) = lof R ι B i y)
    (hn : ∀ i y, e (t (j i y)) = f i (eᵢ i y)) (i : ι) (x : A i) :
    (transportEquiv eᵢ s t e) (lof R ι A i x) = f i x := by
  have hs' (i : ι) (y : B i) : s.symm (lof R ι B i y) = j i y := by
    apply s.injective
    simpa using (hs i y).symm
  simp only [transportEquiv, LinearEquiv.trans_apply, coe_congrLinearEquiv, lmap_lof]
  rw [hs', hn]
  exact congrArg (f i) ((eᵢ i).apply_symm_apply x)

/-- The transported equivalence equals a specified map if its summands do. -/
theorem transportEquiv_toLinearMap
    (eᵢ : ∀ i, B i ≃ₗ[R] A i) (s : C ≃ₗ[R] ⨁ i, B i)
    (t : C ≃ₗ[R] D) (e : D ≃ₗ[R] E)
    (j : ∀ i, B i →ₗ[R] C) (f : (⨁ i, A i) →ₗ[R] E)
    (hs : ∀ i y, s (j i y) = lof R ι B i y)
    (hn : ∀ i y, e (t (j i y)) = f (lof R ι A i (eᵢ i y))) :
    (transportEquiv eᵢ s t e).toLinearMap = f := by
  apply linearMap_ext
  intro i
  ext x
  exact congrLinearEquiv_trans_apply_lof eᵢ s t e j
    (fun i => f.comp (lof R ι A i)) hs hn i x

/-- Canonical summand compatibility makes the specified comparison bijective. -/
theorem bijective_of_transport
    (eᵢ : ∀ i, B i ≃ₗ[R] A i) (s : C ≃ₗ[R] ⨁ i, B i)
    (t : C ≃ₗ[R] D) (e : D ≃ₗ[R] E)
    (j : ∀ i, B i →ₗ[R] C) (f : (⨁ i, A i) →ₗ[R] E)
    (hs : ∀ i y, s (j i y) = lof R ι B i y)
    (hn : ∀ i y, e (t (j i y)) = f (lof R ι A i (eᵢ i y))) :
    Function.Bijective f := by
  rw [← transportEquiv_toLinearMap eᵢ s t e j f hs hn]
  exact (transportEquiv eᵢ s t e).bijective

end DirectSum
