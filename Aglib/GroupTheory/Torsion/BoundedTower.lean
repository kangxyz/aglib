/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.NatInt

/-!
# Vanishing of compatible towers with a uniform power bound


Source: `R5Lab.Aglib.GroupTheory.Torsion.BoundedTower`.
Packet SHA-256:
`a2fdc7152270be69d28d7ee478789ba0bac0f507206d8814ef270de5d0321fdb`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

namespace AddCommGroup
namespace BoundedTower
variable {A : Type*} [AddCommGroup A]

/-- The transition, not mere levelwise finiteness, kills a bounded q-torsion tower. -/
theorem eq_zero_of_compatible_bounded (q e : ℕ) (x : ℕ → A)
    (hstep : ∀ n, q • x (n + 1) = x n)
    (hbound : ∀ n, q ^ e • x n = 0) : ∀ n, x n = 0 := by
  have hiter : ∀ r n, q ^ r • x (n + r) = x n := by
    intro r
    induction r with
    | zero => intro n; simp
    | succ r ih =>
      intro n
      calc
        q ^ (r + 1) • x (n + (r + 1)) =
            q ^ r • (q • x ((n + r) + 1)) := by
          simp only [pow_succ, mul_nsmul, Nat.add_assoc]
          exact smul_comm _ _ _
        _ = q ^ r • x (n + r) := by rw [hstep]
        _ = x n := ih n
  intro n
  exact (hiter e n).symm.trans (hbound (n + e))

end BoundedTower
end AddCommGroup
