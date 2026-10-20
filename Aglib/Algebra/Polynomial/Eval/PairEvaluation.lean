/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.Tactic.Ring

/-!
# Two distinct evaluations and their kernel


Source: `R5Lab.Aglib.Algebra.Polynomial.Eval.PairEvaluation`.
Packet SHA-256:
`ea8fc71d0a2d15216b7c305f95848fe6649c9e86b81f3a7b0060a7f5ddfbdd40`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
open Polynomial
universe u

namespace Polynomial

variable (k : Type u) [Field k] (ρ σ : k)

/-- Both evaluations are retained, without an unlabelled swap. -/
def pairedEvaluation : k[X] →+* k × k := (evalRingHom ρ).prod (evalRingHom σ)

@[simp] lemma pairedEvaluation_C (c : k) :
    pairedEvaluation k ρ σ (C c) = (c, c) := by
  ext <;> simp [pairedEvaluation]

lemma pairedEvaluation_surjective (hneq : ρ ≠ σ) :
    Function.Surjective (pairedEvaluation k ρ σ) := by
  rintro ⟨a, b⟩
  refine ⟨C a + C ((b - a) / (σ - ρ)) * (X - C ρ), ?_⟩
  have hn : σ - ρ ≠ 0 := sub_ne_zero.mpr hneq.symm
  apply Prod.ext
  · simp [pairedEvaluation]
  · change eval σ (C a + C ((b - a) / (σ - ρ)) * (X - C ρ)) = b
    simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X]
    rw [div_mul_cancel₀ _ hn]
    ring

/-- The full evaluation kernel, including nilpotent structure. -/
lemma pairedEvaluation_ker (hneq : ρ ≠ σ) :
    RingHom.ker (pairedEvaluation k ρ σ) = Ideal.span {(X - C ρ) * (X - C σ)} := by
  ext p
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hp
    change pairedEvaluation k ρ σ p = 0 at hp
    have hpρ : eval ρ p = 0 := congrArg Prod.fst hp
    have hpσ : eval σ p = 0 := congrArg Prod.snd hp
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hpρ
    have hqσ : eval σ q = 0 := by
      have h := congrArg (eval σ) hq
      rw [hpσ, eval_mul, eval_sub, eval_X, eval_C] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr hneq.symm)
    obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hqσ
    refine ⟨r, ?_⟩
    rw [hq, hr, mul_assoc]
  · rintro ⟨q, rfl⟩
    change pairedEvaluation k ρ σ (((X - C ρ) * (X - C σ)) * q) = 0
    ext <;> simp [pairedEvaluation]

end Polynomial
