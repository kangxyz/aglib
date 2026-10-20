/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Data.Nat.Basic

/-!
# Positive product factors for divisible natural levels

The quotient-positivity and multiplication formulas reuse `Nat.div_pos`
and `Nat.mul_div_cancel'`.

Source: `R5Lab.Aglib.Data.Nat.PositiveDivisibility`.
Packet SHA-256:
`b42c7a02e6e1c15f4196404e11ae4bdfa82ccd3343fd14a8400170f19057d46f`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

namespace Nat

/-- Positive divisible levels are covered by a positive product factor. -/
theorem exists_pos_mul_eq_of_dvd {d m : ℕ} (h : d ∣ m) (hd : 0 < d) (hm : 0 < m) :
    ∃ e : ℕ, 0 < e ∧ m = d * e :=
  ⟨m / d, Nat.div_pos (Nat.le_of_dvd hm h) hd, (Nat.mul_div_cancel' h).symm⟩

end Nat
