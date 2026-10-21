/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic.Abel

/-!
# Constancy along a complementary cyclic chain

Equal values along every predecessor edge except one force constancy on the same finite cyclic
index.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Curves/LocalModels/CyclicModelComparison/PresentationComponents.lean`: source
ranges [[447, 470]];
SHA-256 `77de4d0bb9d6dc601d58a053264a6559eaf17efb65cc7177282388708ff2cf7c`.
-/

@[expose] public noncomputable section

open Equiv
namespace Equiv.Perm

theorem cyclic_values_constant {n : ℕ} {A : Type*} (v : Fin n → A) (i : Fin n)
    (h : ∀ j, j ≠ i → v ((finRotate n).symm j) = v j) : ∀ j, v j = v i := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    have ha : ∀ j : Fin (n + 1), v (i + j) = v i := by
      intro j
      induction j using Fin.induction with
      | zero => simp
      | succ j ih =>
        have hne : i + j.succ ≠ i := by
          intro hi
          have hx : i + j.succ = i + 0 := by simpa only [add_zero] using hi
          exact j.succ_ne_zero (add_left_cancel hx)
        have he := h (i + j.succ) hne
        rw [finRotate_symm_apply, ← Fin.coeSucc_eq_succ] at he
        have hx : i + (j.castSucc + 1) - 1 = i + j.castSucc := by abel
        rw [hx] at he
        simpa only [Fin.coeSucc_eq_succ] using he.symm.trans ih
    intro j
    have hx : i + (j - i) = j := by abel
    simpa only [hx] using ha (j - i)


end Equiv.Perm
