/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.Order

/-!
# Fixed points and invariant functions of finite rotation


Source: `R5Lab.Aglib.Data.Fin.Rotate`.
Packet SHA-256:
`93f34f5e9007bb463602a2c0ec6b328ed21e6a9d083b01534bf786d537eccff0`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

namespace Fin

/-- Invariance under the actual cyclic successor forces every value equal. -/
theorem apply_eq_apply_zero_of_rotate_invariant {α : Type*} (n : ℕ) (f : Fin (n + 1) → α)
    (h : ∀ i, f (finRotate (n + 1) i) = f i) (i : Fin (n + 1)) : f i = f 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i hi =>
    have hr : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
    rw [← hr, h]
    exact hi


variable (n : ℕ)

/-- Every component of a polygon of length greater than one has distinct endpoint nodes. -/
theorem finRotate_ne_self_of_one_lt (hn : 1 < n) (i : Fin n) : finRotate n i ≠ i := by
  let : NeZero n := ⟨by omega⟩
  intro h
  have hv : (i.val + 1) % n = i.val := by
    simpa only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hn] using
      congrArg Fin.val h
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have he : i.val + 1 = n := by omega
    rw [he, Nat.mod_self] at hv
    have := i.isLt
    omega


/-- The preceding node and following node are distinct whenever n>1. -/
theorem finRotate_symm_ne_self_of_one_lt (hn : 1 < n) (i : Fin n) : (finRotate n).symm i ≠ i := by
  intro h
  apply finRotate_ne_self_of_one_lt n hn i
  exact (congrArg (finRotate n) h.symm).trans ((finRotate n).apply_symm_apply i)

end Fin
