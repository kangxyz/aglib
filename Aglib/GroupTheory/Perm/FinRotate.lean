/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Centralizer and order of finite rotation


Source: `R5Lab.Aglib.GroupTheory.Perm.FinRotate`.
Packet SHA-256:
`6e8a3ac0f267b99c8e8f3844e7f318f1c68f014323a06e1101da4315ffdb569a`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section

namespace Equiv.Perm

variable (n : ℕ)

/-- Actual permutations preserving the cyclic endpoint equations. -/
abbrev finRotateCentralizer := Subgroup.centralizer ({finRotate n} : Set (Equiv.Perm (Fin n)))


/-- The actual successor permutation, with its endpoint-compatibility proof. -/
def finRotateInCentralizer : finRotateCentralizer n :=
  ⟨finRotate n, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩


/-- Positive cycles have exact period n, including the one-gon identity case. -/
theorem finRotate_order [NeZero n] : orderOf (finRotate n) = n := by
  by_cases hn : n = 1
  · subst n
    have h : finRotate 1 = (1 : Equiv.Perm (Fin 1)) := Subsingleton.elim _ _
    rw [h, orderOf_one]
  · have h2 : 2 ≤ n := by have := NeZero.ne n; omega
    rw [(isCycle_finRotate_of_le h2).orderOf, support_finRotate_of_le h2]
    simp

end Equiv.Perm
