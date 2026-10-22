/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Filtration

/-! # Finite-order separation of a bounded submodule

Artin–Rees separates a submodule killed by a fixed ideal power from a sufficiently
high power filtration of its finite ambient module. This yields a finite-stage
joint monomorphism in geometric bounded reconstruction, without assuming that
arbitrary inverse-limit sheaves are quasicoherent.
-/

@[expose] public section

namespace Submodule

universe u v
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A bounded submodule has zero intersection with a sufficiently high power
of the original ideal in its finite ambient module. -/
theorem exists_pow_smul_top_inf_eq_bot_of_pow_smul_eq_bot
    (I : Ideal R) (N : Submodule R M) (t : ℕ) (h : I ^ t • N = ⊥) :
    ∃ n : ℕ, I ^ n • (⊤ : Submodule R M) ⊓ N = ⊥ := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul N
  refine ⟨k + t, le_antisymm ?_ bot_le⟩
  rw [hk (k + t) (Nat.le_add_right k t), Nat.add_sub_cancel_left]
  exact (smul_mono_right (I ^ t) inf_le_right).trans h.le

end Submodule
