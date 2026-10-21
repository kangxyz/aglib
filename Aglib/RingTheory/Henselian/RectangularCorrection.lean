/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.DeterminantCorrection
public import Mathlib.Logic.Equiv.Set

/-!
# Selected-minor correction with the actual source free coordinates fixed

A rectangular system is reduced to the square determinant-correction theorem
by substituting the current source point's free coordinates, not by freezing
formal coordinates before choosing a source approximation. The free variable
index need not be finite, and the selected determinant can vanish or be a zero divisor.
-/

@[expose] public noncomputable section

namespace HenselianLocalRing

open MvPolynomial

universe u v w

variable {R : Type u} {σ : Type v} {τ : Type w} [CommRing R]

/-- Substitute actual source values only for the free coordinates. -/
def partialEvalFree (z : τ → R) : MvPolynomial (σ ⊕ τ) R →ₐ[R] MvPolynomial σ R :=
  aeval (Sum.elim X (C ∘ z))

/-- Partial evaluation is evaluation at the literal combined source point. -/
theorem eval_partialEvalFree (f : MvPolynomial (σ ⊕ τ) R) (z : τ → R) (x : σ → R) :
    eval x (partialEvalFree z f) = eval (Sum.elim x z) f := by
  simpa only [partialEvalFree, aeval_eq_eval, Algebra.algebraMap_self,
    Function.comp_def, RingHom.id_apply] using (aeval_sumElim (S := R) (T := R) f z x).symm

/-- The selected derivatives commute with substitution of the actual free values. -/
theorem pderiv_partialEvalFree (f : MvPolynomial (σ ⊕ τ) R) (z : τ → R) (j : σ) :
    pderiv j (partialEvalFree z f) = partialEvalFree z (pderiv (Sum.inl j) f) :=
  (aeval_sumElim_pderiv_inl f z j).symm

variable [HenselianLocalRing R] [Fintype σ] [DecidableEq σ]

/-- Rectangular selected-minor correction, fixing all actual free source coordinates exactly. -/
theorem exists_eval_eq_zero_of_mem_selected_det_sq_mul
    (F : σ → MvPolynomial (σ ⊕ τ) R) (y₀ : σ ⊕ τ → R)
    (a : Ideal R) (ha : a ≠ ⊤)
    (hF : ∀ i, eval y₀ (F i) ∈
      Ideal.span {Matrix.det (Matrix.of fun i j ↦ eval y₀ (pderiv (Sum.inl j) (F i))) ^ 2} * a) :
    ∃ y : σ ⊕ τ → R, (∀ i, eval y (F i) = 0) ∧
      (∀ j, y (Sum.inr j) = y₀ (Sum.inr j)) ∧
      (∀ i, y (Sum.inl i) - y₀ (Sum.inl i) ∈
        Ideal.span {Matrix.det (Matrix.of fun i j ↦ eval y₀ (pderiv (Sum.inl j) (F i)))} * a) ∧
      ∀ k, y k - y₀ k ∈ a := by
  let x₀ : σ → R := fun i => y₀ (Sum.inl i)
  let z : τ → R := fun j => y₀ (Sum.inr j)
  let G : σ → MvPolynomial σ R := fun i => partialEvalFree z (F i)
  have hpoint : Sum.elim x₀ z = y₀ := by
    funext k
    cases k <;> rfl
  have hG (i : σ) : eval x₀ (G i) = eval y₀ (F i) := by
    change eval x₀ (partialEvalFree z (F i)) = _
    rw [eval_partialEvalFree, hpoint]
  have hJ : Matrix.of (fun i j => eval x₀ (pderiv j (G i))) =
      Matrix.of (fun i j => eval y₀ (pderiv (Sum.inl j) (F i))) := by
    ext i j
    change eval x₀ (pderiv j (partialEvalFree z (F i))) =
      eval y₀ (pderiv (Sum.inl j) (F i))
    rw [pderiv_partialEvalFree, eval_partialEvalFree, hpoint]
  have herror : ∀ i, eval x₀ (G i) ∈
      Ideal.span {Matrix.det (Matrix.of fun i j => eval x₀ (pderiv j (G i))) ^ 2} * a := by
    intro i
    rw [hG, hJ]
    exact hF i
  obtain ⟨x, hx, hxa⟩ := exists_eval_eq_zero_of_mem_det_sq_mul G x₀ a ha herror
  refine ⟨Sum.elim x z, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← eval_partialEvalFree]
    exact hx i
  · intro j
    rfl
  · intro i
    change x i - x₀ i ∈ _
    simpa only [hJ] using hxa i
  · intro k
    cases k with
    | inl i =>
      exact Ideal.mul_le_right (hxa i)
    | inr j =>
      change y₀ (Sum.inr j) - y₀ (Sum.inr j) ∈ a
      rw [sub_self]
      exact a.zero_mem

/-- Correction for an arbitrary actual selected-column embedding. Coordinates outside
its range stay equal to the current source point. -/
theorem exists_eval_eq_zero_of_mem_embedding_det_sq_mul
    {ν : Type*} (e : σ ↪ ν) (F : σ → MvPolynomial ν R) (y₀ : ν → R)
    (a : Ideal R) (ha : a ≠ ⊤)
    (hF : ∀ i, eval y₀ (F i) ∈
      Ideal.span {Matrix.det (Matrix.of fun i j ↦ eval y₀ (pderiv (e j) (F i))) ^ 2} * a) :
    ∃ y : ν → R, (∀ i, eval y (F i) = 0) ∧
      (∀ k, k ∉ Set.range e → y k = y₀ k) ∧
      (∀ i, y (e i) - y₀ (e i) ∈
        Ideal.span {Matrix.det (Matrix.of fun i j ↦ eval y₀ (pderiv (e j) (F i)))} * a) ∧
      ∀ k, y k - y₀ k ∈ a := by
  classical
  let E : σ ⊕ {k : ν // k ∉ Set.range e} ≃ ν :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range e))
  have hE (i : σ) : E (Sum.inl i) = e i := rfl
  have hEs (i : σ) : E.symm (e i) = Sum.inl i := by
    apply E.injective
    rw [E.apply_symm_apply, hE]
  let G : σ → MvPolynomial (σ ⊕ {k : ν // k ∉ Set.range e}) R := fun i => rename E.symm (F i)
  let x₀ := y₀ ∘ E
  have heval (f : MvPolynomial ν R) : eval x₀ (rename E.symm f) = eval y₀ f := by
    rw [eval_rename]
    have hc : x₀ ∘ E.symm = y₀ := by
      funext k
      exact congrArg y₀ (E.apply_symm_apply k)
    rw [hc]
  have hJ : Matrix.of (fun i j => eval x₀ (pderiv (Sum.inl j) (G i))) =
      Matrix.of (fun i j => eval y₀ (pderiv (e j) (F i))) := by
    ext i j
    change eval x₀ (pderiv (Sum.inl j) (rename E.symm (F i))) =
      eval y₀ (pderiv (e j) (F i))
    rw [← hEs, pderiv_rename E.symm.injective, heval]
  have herror : ∀ i, eval x₀ (G i) ∈
      Ideal.span {Matrix.det (Matrix.of fun i j =>
        eval x₀ (pderiv (Sum.inl j) (G i))) ^ 2} * a := by
    intro i
    rw [hJ]
    exact (heval (F i)).symm ▸ hF i
  obtain ⟨x, hx, hfree, hselected, hclose⟩ :=
    exists_eval_eq_zero_of_mem_selected_det_sq_mul G x₀ a ha herror
  refine ⟨x ∘ E.symm, ?_, ?_, ?_, ?_⟩
  · intro i
    have h := hx i
    change eval x (rename E.symm (F i)) = 0 at h
    rwa [eval_rename] at h
  · intro k hk
    have hEk : E (Sum.inr ⟨k, hk⟩) = k := rfl
    have hEs' : E.symm k = Sum.inr ⟨k, hk⟩ := by
      apply E.injective
      rw [E.apply_symm_apply, hEk]
    change x (E.symm k) = y₀ k
    rw [hEs', hfree]
    exact congrArg y₀ hEk
  · intro i
    change x (E.symm (e i)) - y₀ (e i) ∈ _
    rw [hEs]
    have h := hselected i
    rw [hJ] at h
    exact h
  · intro k
    have h := hclose (E.symm k)
    change x (E.symm k) - y₀ (E (E.symm k)) ∈ a at h
    change x (E.symm k) - y₀ k ∈ a
    simpa only [E.apply_symm_apply] using h

end HenselianLocalRing
