/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Self-injectivity of a positive-modulus ZMod ring

For every positive modulus, including one and composite moduli, `ZMod n` is an
injective module over itself. Baer's criterion is proved on the original ring:
pull an ideal back to the integers, take a generator `d`, and write `n = d * k`.
The image of `d` is annihilated by `k`; cancellation in the integers shows that
it is divisible by `d`, so multiplication by the quotient extends the given map.
No character-module or alternative quotient-ring realization is introduced.

The source is this elementary principal-ideal argument and Mathlib's
`Algebra/Module/Injective.lean`, `Module.Baer.injective`. Positivity is necessary:
the assertion is false for `ZMod 0 = ℤ`.
-/

@[expose] public noncomputable section

namespace ZMod

variable (n : ℕ) [NeZero n]

/-- Baer's extension criterion for the original positive-modulus ring `ZMod n`. -/
theorem baer_self : Module.Baer (ZMod n) (ZMod n) := by
  intro I f
  let J : Ideal ℤ := I.comap (Int.castRingHom (ZMod n))
  let d : ℤ := Submodule.IsPrincipal.generator J
  have hd : (d : ZMod n) ∈ I := Submodule.IsPrincipal.generator_mem J
  have hnJ : (n : ℤ) ∈ J := by
    simp [J]
  obtain ⟨k, hk⟩ : d ∣ (n : ℤ) :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd J).mp hnJ
  have hk0 : k ≠ 0 := by
    intro h
    have : (n : ℤ) = 0 := by simpa [h] using hk
    exact NeZero.ne n (Int.natCast_eq_zero.mp this)
  let a : I := ⟨(d : ZMod n), hd⟩
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective (f a)
  have hka : (k : ZMod n) • a = 0 := by
    apply Subtype.ext
    change (k : ZMod n) * (d : ZMod n) = 0
    rw [mul_comm, ← Int.cast_mul, ← hk]
    simp
  have hkb : ((k * b : ℤ) : ZMod n) = 0 := by
    rw [Int.cast_mul, hb]
    change (k : ZMod n) • f a = 0
    rw [← map_smul, hka, map_zero]
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (k * b) n).mp hkb
  have hbc : b = d * c := by
    apply mul_left_cancel₀ hk0
    calc
      k * b = (n : ℤ) * c := hc
      _ = k * (d * c) := by rw [hk]; ring
  refine ⟨(LinearMap.id : ZMod n →ₗ[ZMod n] ZMod n).smulRight (c : ZMod n), ?_⟩
  intro x hx
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have hz : z ∈ J := hx
  obtain ⟨t, ht⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd J).mp hz
  have hza : (⟨(z : ZMod n), hx⟩ : I) = (t : ZMod n) • a := by
    apply Subtype.ext
    change (z : ZMod n) = (t : ZMod n) * (d : ZMod n)
    rw [ht, Int.cast_mul, mul_comm]
  change (z : ZMod n) * (c : ZMod n) = f ⟨(z : ZMod n), hx⟩
  rw [hza, map_smul, ← hb, hbc, ht, Int.cast_mul, Int.cast_mul]
  change (d : ZMod n) * t * c = (t : ZMod n) * (d * c)
  ring

/-- The original ring `ZMod n` is self-injective for every nonzero modulus. -/
theorem injective_self : Module.Injective (ZMod n) (ZMod n) :=
  (baer_self n).injective

/-- Every linear functional extends across an injective linear map, at independent universes. -/
theorem exists_dual_extension {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod n) M] [Module (ZMod n) N] (f : M →ₗ[ZMod n] N)
    (hf : Function.Injective f) (g : M →ₗ[ZMod n] ZMod n) :
    ∃ h : N →ₗ[ZMod n] ZMod n, h.comp f = g :=
  (baer_self n).extension_property f hf g

end ZMod
