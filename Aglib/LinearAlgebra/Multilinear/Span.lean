/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Multilinear maps on spans

For a commutative semiring `R`, a multilinear map `f` in finitely many variables and a set `T`,
`MultilinearMap.map_mem_span_of_forall_mem_span` shows that `f` sends a family of vectors of
`span R T` into the span of the values of `f` on families of vectors of `T`.
-/

@[expose] public section

open Function

namespace MultilinearMap

variable {R ι M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- A multilinear map sends a family of vectors of `span R T` into the span of its values on the
families of vectors of `T`. -/
theorem map_mem_span_of_forall_mem_span [Finite ι] (f : MultilinearMap R (fun _ : ι => M) N)
    {T : Set M} {v : ι → M} (hv : ∀ i, v i ∈ Submodule.span R T) :
    f v ∈ Submodule.span R {x | ∃ w : ι → M, (∀ i, w i ∈ T) ∧ f w = x} := by
  classical
  cases nonempty_fintype ι
  set J := Submodule.span R {x | ∃ w : ι → M, (∀ i, w i ∈ T) ∧ f w = x}
  suffices H : ∀ s : Finset ι, ∀ w : ι → M, (∀ i ∈ s, w i ∈ Submodule.span R T) →
      (∀ i ∉ s, w i ∈ T) → f w ∈ J from
    H Finset.univ v (fun i _ => hv i) fun i hi => absurd (Finset.mem_univ i) hi
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro w _ hw
    exact Submodule.subset_span ⟨w, fun i => hw i (Finset.notMem_empty i), rfl⟩
  | insert a s ha ih =>
    intro w hs hns
    have key : ∀ x ∈ Submodule.span R T, f (update w a x) ∈ J := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        refine ih _ (fun i hi => ?_) fun i hi => ?_
        · rw [update_of_ne (by rintro rfl; exact ha hi)]
          exact hs i (Finset.mem_insert_of_mem hi)
        · by_cases hia : i = a
          · subst hia
            simpa using hx
          · rw [update_of_ne hia]
            exact hns i (by simp [hia, hi])
      | zero => simp [f.map_update_zero]
      | add x y _ _ hx hy =>
        rw [f.map_update_add]
        exact J.add_mem hx hy
      | smul c x _ hx =>
        rw [f.map_update_smul]
        exact J.smul_mem c hx
    simpa using key (w a) (hs a (Finset.mem_insert_self a s))

end MultilinearMap
