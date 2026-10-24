/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Tactic.Ring

/-! # Principal units of a square-zero kernel

Raising a principal unit to an invertible natural power has a unique
principal root. These statements use the actual original ring map.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.Invertible.Root

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

private theorem one_add_pow_of_sq_zero (a : R) (ha : a ^ 2 = 0) (n : ℕ) :
    (1 + a) ^ n = 1 + (n : R) * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    calc
      (1 + (n : R) * a) * (1 + a) =
          1 + ((n : R) + 1) * a + (n : R) * a ^ 2 := by ring
      _ = 1 + ((n + 1 : ℕ) : R) * a := by
        rw [ha, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]

private theorem sq_zero_of_kernel (φ : R →+* S) (hφ : RingHom.ker φ ^ 2 = ⊥)
    (a : R) (ha : φ a = 0) : a ^ 2 = 0 := by
  have hamem : a ∈ RingHom.ker φ := ha
  have hmem : a ^ 2 ∈ RingHom.ker φ ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hamem hamem
  rw [hφ] at hmem
  exact Ideal.mem_bot.mp hmem

/-- An actual principal unit has an actual principal root at every invertible exponent. -/
theorem exists_principal_unit_root_of_square_zero
    (φ : R →+* S) (hφ : RingHom.ker φ ^ 2 = ⊥) (n : ℕ) (hn : IsUnit (n : R))
    (a : Rˣ) (ha : φ (a : R) = 1) :
    ∃ b : Rˣ, φ (b : R) = 1 ∧ b ^ n = a := by
  obtain ⟨c, hc⟩ := hn
  let t : R := (a : R) - 1
  have htφ : φ t = 0 := by simp only [t, map_sub, map_one, ha, sub_self]
  have ht : t ^ 2 = 0 := sq_zero_of_kernel φ hφ t htφ
  let s : R := (↑c⁻¹ : R) * t
  have hs : s ^ 2 = 0 := by simp only [s, mul_pow, ht, mul_zero]
  let b : Rˣ := {
    val := 1 + s
    inv := 1 - s
    val_inv := by
      calc
        (1 + s) * (1 - s) = 1 - s ^ 2 := by ring
        _ = 1 := by rw [hs, sub_zero]
    inv_val := by
      calc
        (1 - s) * (1 + s) = 1 - s ^ 2 := by ring
        _ = 1 := by rw [hs, sub_zero] }
  refine ⟨b, ?_, ?_⟩
  · change φ (1 + s) = 1
    simp only [s, map_add, map_mul, map_one, htφ, mul_zero, add_zero]
  · apply Units.ext
    change (1 + s) ^ n = (a : R)
    rw [one_add_pow_of_sq_zero s hs]
    have hc' : (n : R) * (↑c⁻¹ : R) = 1 := by
      rw [← hc]
      exact Units.mul_inv c
    calc
      1 + (n : R) * s = 1 + t := by
        dsimp only [s]
        rw [← mul_assoc, hc', one_mul]
      _ = (a : R) := by dsimp only [t]; ring

/-- A principal unit whose invertible power is one is already one. -/
theorem principal_unit_eq_one_of_pow_eq_one_of_square_zero
    (φ : R →+* S) (hφ : RingHom.ker φ ^ 2 = ⊥) (n : ℕ) (hn : IsUnit (n : R))
    (a : Rˣ) (ha : φ (a : R) = 1) (hpow : a ^ n = 1) : a = 1 := by
  let t : R := (a : R) - 1
  have htφ : φ t = 0 := by simp only [t, map_sub, map_one, ha, sub_self]
  have ht : t ^ 2 = 0 := sq_zero_of_kernel φ hφ t htφ
  have hp : (a : R) ^ n = 1 := congrArg Units.val hpow
  have he : 1 + t = (a : R) := by dsimp only [t]; ring
  have hmul : (n : R) * t = 0 := by
    apply add_left_cancel (a := (1 : R))
    calc
      1 + (n : R) * t = (1 + t) ^ n := (one_add_pow_of_sq_zero t ht n).symm
      _ = 1 + 0 := by rw [he, hp, add_zero]
  obtain ⟨c, hc⟩ := hn
  have ht0 : t = 0 := by
    have h := congrArg (fun z : R => (↑c⁻¹ : R) * z) hmul
    rw [← hc, ← mul_assoc, Units.inv_mul, one_mul, mul_zero] at h
    exact h
  apply Units.ext
  exact sub_eq_zero.mp ht0

end AlgebraicGeometry.Scheme.Modules.Invertible.Root
