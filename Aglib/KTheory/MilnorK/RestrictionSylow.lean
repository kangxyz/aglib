/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.RestrictionKernel
public import Aglib.FieldTheory.SylowFixedField

/-!
# Joint detection by actual Sylow fixed-field restrictions

The already proved finite separable degree retraction supplies annihilators.
The Sylow fixed-field degrees are prime to their respective primes, and these
annihilators jointly detect every original Milnor class. No canonical transfer
or norm tower is assumed in this descent statement.
-/

@[expose] public noncomputable section

namespace MilnorK

private theorem eq_zero_of_prime_coprime_annihilators {A : Type*} [AddGroup A]
    (x : A) (hx : ∀ p : ℕ, p.Prime → ∃ m : ℕ, p.Coprime m ∧ m • x = 0) : x = 0 := by
  apply AddMonoid.addOrderOf_eq_one_iff.mp
  by_contra h
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
  obtain ⟨m, hm, hmx⟩ := hx p hp
  exact (hp.coprime_iff_not_dvd.mp hm)
    (hpd.trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hmx))

variable (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω]
  [FiniteDimensional k Ω] [IsGalois k Ω]

/-- The actual restrictions to one Sylow fixed field for each prime jointly
separate all original Milnor classes. -/
theorem eq_zero_of_sylow_restrictions (n : ℕ) (x : K k n)
    (hx : ∀ (p : ℕ) (_hp : p.Prime),
      ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
        map n (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) x = 0) : x = 0 := by
  apply eq_zero_of_prime_coprime_annihilators x
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := hx p hp
  refine ⟨Module.finrank k (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω))),
    IntermediateField.coprime_finrank_sylow_fixedField p S, ?_⟩
  simpa only [natCast_zsmul] using finrank_smul_eq_zero_of_map_eq_zero k
    (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω))) n x hS

/-- Equality descends through the actual finite Sylow restriction family. -/
theorem eq_of_sylow_restrictions (n : ℕ) (x y : K k n)
    (hxy : ∀ (p : ℕ) (_hp : p.Prime),
      ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
        map n (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) x =
        map n (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) y) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_sylow_restrictions k Ω n (x - y)
  intro p hp
  obtain ⟨S, hS⟩ := hxy p hp
  exact ⟨S, by rw [map_sub, hS, sub_self]⟩

end MilnorK
