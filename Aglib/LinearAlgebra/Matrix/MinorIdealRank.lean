/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FittingIdeal.Minors
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Vanishing maximal minors produce a row relation

Over a field, vanishing of the whole ideal of maximal minors produces an actual
nonzero relation between the rows. Applied over a residue field, this supplies the
relation used by a unit-pivot change of generators in a Néron modification.
-/

@[expose] public section

namespace Matrix

variable {K m : Type*} [Field K] [Finite m] {r : ℕ}

/-- If all maximal minors vanish, the rows admit an actual nonzero linear relation. -/
theorem exists_row_relation_of_minorIdeal_eq_bot (A : Matrix (Fin r) m K)
    (h : A.minorIdeal r = ⊥) :
    ∃ b : Fin r → K, b ≠ 0 ∧ ∀ j, ∑ i, b i * A i j = 0 := by
  classical
  let := Fintype.ofFinite m
  have hdep : ¬LinearIndependent K A.row := by
    intro hind
    have hspan : Submodule.span K (Set.range Aᵀ) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have hrank := hind.rank_matrix
      rw [rank_eq_finrank_span_cols] at hrank
      change Module.finrank K (Submodule.span K (Set.range Aᵀ)) =
        Fintype.card (Fin r) at hrank
      simpa only [Module.finrank_fintype_fun_eq_card] using hrank
    have hone : (1 : K) ∈ (⊤ : Submodule K (Fin r → K)).minorIdeal r := by
      have hid := Submodule.det_mem_minorIdeal
        (N := (⊤ : Submodule K (Fin r → K)))
        (v := (1 : Matrix (Fin r) (Fin r) K)) (fun _ => Submodule.mem_top) id
      change (1 : Matrix (Fin r) (Fin r) K).det ∈
        (⊤ : Submodule K (Fin r → K)).minorIdeal r at hid
      simpa only [det_one] using hid
    rw [minorIdeal_eq_minorIdeal_span, hspan] at h
    rw [h] at hone
    simp at hone
  obtain ⟨b, hb, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨b, ?_, ?_⟩
  · intro hz
    exact hi (congrFun hz i)
  · intro j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, row_apply,
      Pi.zero_apply] using congrFun hb j

end Matrix
