/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Filtration

/-!
# An Artin–Rees test extension

For ideals `I` and `𝔪` of a Noetherian ring `P` there is `m ≥ 1` with
`I ⊓ 𝔪 * (I ⊔ 𝔪 ^ m) = 𝔪 * I`. Equivalently, for `J := I + 𝔪 ^ m`, the map
`I / 𝔪 I → J / 𝔪 J` induced by `I ≤ J` is injective. This is the ideal arithmetic
of the Artinian-test criterion for formal smoothness: the square-zero extension
`P / 𝔪 J → P / J` detects the Jacobian criterion for `P / I` (Kleiman, *The
Picard scheme*, arXiv:math/0504020v1, proof of Prop. 5.19, p. 47, uses the
infinitesimal criterion on Artin local test rings; this lemma is the step that
makes one such test ring suffice). The source is the Artin–Rees lemma
`Ideal.exists_pow_inf_eq_pow_smul`. The ring is Noetherian; no local or
field hypothesis is used.
-/

@[expose] public section

namespace Ideal

variable {P : Type*} [CommRing P] [IsNoetherianRing P]

/-- **Artin–Rees test extension.** For ideals `I` and `𝔪` of a Noetherian ring
there is `m ≥ 1` with `I ⊓ 𝔪 * (I ⊔ 𝔪 ^ m) = 𝔪 * I`. -/
theorem exists_inf_mul_sup_pow_eq_mul (I 𝔪 : Ideal P) :
    ∃ m : ℕ, 0 < m ∧ I ⊓ 𝔪 * (I ⊔ 𝔪 ^ m) = 𝔪 * I := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔪 (I : Submodule P P)
  refine ⟨k + 1, Nat.succ_pos k, ?_⟩
  have hAR : 𝔪 ^ (k + 2) ⊓ I ≤ 𝔪 * I := by
    have h := hk (k + 2) (by omega)
    simp only [Nat.add_sub_cancel_left, Ideal.smul_eq_mul, Ideal.mul_top] at h
    calc 𝔪 ^ (k + 2) ⊓ I = 𝔪 ^ 2 * (𝔪 ^ k ⊓ I) := h
      _ ≤ 𝔪 ^ 2 * I := Ideal.mul_mono_right inf_le_right
      _ = 𝔪 * (𝔪 * I) := by rw [pow_two, mul_assoc]
      _ ≤ 𝔪 * I := Ideal.mul_le_right
  have hmul : 𝔪 * (I ⊔ 𝔪 ^ (k + 1)) = 𝔪 * I ⊔ 𝔪 ^ (k + 2) := by
    rw [Ideal.mul_sup, ← pow_succ']
  rw [hmul, inf_comm, sup_inf_assoc_of_le _ (Ideal.mul_le_right : 𝔪 * I ≤ I)]
  exact sup_eq_left.mpr hAR

end Ideal
