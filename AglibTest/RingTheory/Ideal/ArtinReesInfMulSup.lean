/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.ArtinReesInfMulSup

/-!
# Consumer checks for the Artin–Rees test extension

`Ideal.exists_inf_mul_sup_pow_eq_mul` for ideals of a Noetherian ring, and its consequence
`I ⊓ 𝔪 * (I ⊔ 𝔪 ^ m) ≤ 𝔪 * I`; axiom guard.
-/

@[expose] public section

namespace AglibTest.ArtinReesInfMulSup

variable {P : Type*} [CommRing P] [IsNoetherianRing P]

/-- The identity yields the inclusion used for the injectivity of `I / 𝔪 I → J / 𝔪 J`. -/
example (I 𝔪 : Ideal P) : ∃ m : ℕ, 0 < m ∧ I ⊓ 𝔪 * (I ⊔ 𝔪 ^ m) ≤ 𝔪 * I := by
  obtain ⟨m, hm, h⟩ := Ideal.exists_inf_mul_sup_pow_eq_mul I 𝔪
  exact ⟨m, hm, h.le⟩

end AglibTest.ArtinReesInfMulSup

/--
info: 'Ideal.exists_inf_mul_sup_pow_eq_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.exists_inf_mul_sup_pow_eq_mul
