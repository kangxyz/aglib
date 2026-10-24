/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Finiteness.Defs

/-! # A uniform additive annihilator for finite modules

Finite generation over the scalar semiring, not finiteness of the underlying
set, turns elementwise additive torsion into a positive uniform annihilator.
The scalar semiring need not be Noetherian or finite.
-/

@[expose] public noncomputable section

namespace Module.Finite

variable (R : Type*) {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [Module.Finite R M]

include R

/-- An additively torsion finite module has one positive integer annihilating
all its elements, even when its underlying set is infinite. -/
theorem exists_pos_nsmul_eq_zero_of_isAddTorsion (hM : IsAddTorsion M) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : M, n • x = 0 := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := R) (M := M))
  let n := ∏ x ∈ s, addOrderOf x
  have hn : 0 < n := Finset.prod_pos (fun x _ => (hM x).addOrderOf_pos)
  let f : M →ₗ[R] M := n • LinearMap.id
  have hker : (⊤ : Submodule R M) ≤ LinearMap.ker f := by
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    change n • x = 0
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (Finset.dvd_prod_of_mem _ hx)
  refine ⟨n, hn, fun x => ?_⟩
  exact hker (Submodule.mem_top (R := R) (x := x))

/-- The same uniform bound as an equation of the original linear endomorphism. -/
theorem exists_pos_nsmul_id_eq_zero_of_isAddTorsion (hM : IsAddTorsion M) :
    ∃ n : ℕ, 0 < n ∧ n • (LinearMap.id : M →ₗ[R] M) = 0 := by
  obtain ⟨n, hn, hzero⟩ := exists_pos_nsmul_eq_zero_of_isAddTorsion R hM
  refine ⟨n, hn, ?_⟩
  ext x
  exact hzero x

end Module.Finite
