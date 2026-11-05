/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Positive additive annihilators of finite-type torsion modules

A finite generating set over the original scalar ring has a common positive
additive annihilator. Scalar multiplication commutes with natural multiples,
so the same integer kills the whole module. The ring and additive group need
not be finite, and the ring need not be Noetherian.
-/

@[expose] public section
namespace Module

universe r m

/-- Finite generation over an arbitrary semiring turns elementwise additive
torsion into a positive annihilator of the original whole module. -/
theorem exists_positive_annihilator_of_isAddTorsion
    (R : Type r) [Semiring R] (M : Type m) [AddCommMonoid M] [Module R M]
    [Module.Finite R M] (hM : IsAddTorsion M) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : M, n • x = 0 := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R M).FG)
  choose k hk hkzero using fun x : M => (hM x).exists_nsmul_eq_zero
  let n : ℕ := ∏ x ∈ s, k x
  refine ⟨n, Finset.prod_pos (fun x _ => hk x), ?_⟩
  intro x
  have hx : x ∈ Submodule.span R (s : Set M) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem k hy
      change n • y = 0
      rw [show n = k y * d from hd, mul_nsmul, hkzero y, smul_zero]
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]

end Module
