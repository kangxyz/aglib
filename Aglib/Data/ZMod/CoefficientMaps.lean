/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Cyclic coefficient insertion across divisible levels

Reduction reuses `ZMod.castHom`; insertion multiplies integer representatives
by the actual quotient of levels. Positive target level remains necessary
for the injectivity theorem.

Source: `R5Lab.Aglib.Data.ZMod.CoefficientMaps`.
Packet SHA-256:
`436f5a1c977724d7164ddbe5ff3cc479b1d808d5d695d9b710a093fda020c401`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

namespace ZMod

variable {d n : ℕ}


/-- Additive coefficient divisorInsertion `j_{d,n}` in
`K2-018#eq:k2018-coefficient-compatibility`, on the module source basis.
Integer multiplication by `n / d` is shown to kill `d`, so the induced map is
well-defined. This is divisorInsertion in a common rank-one Tate lattice, rather than
the tensor square of an inclusion of roots of unity. -/
def divisorInsertion (h : d ∣ n) : ZMod d →+ ZMod n :=
  ZMod.lift d ⟨
    { toFun := fun a : ℤ => (a : ZMod n) * (n / d : ℕ)
      map_zero' := by simp
      map_add' := by intro a b; simp [add_mul] }, by
    change (((d : ℕ) : ℤ) : ZMod n) * (n / d : ℕ) = 0
    rw [Int.cast_natCast, ← Nat.cast_mul, Nat.mul_div_cancel' h, ZMod.natCast_self]⟩

/-- Integer-representative formula for the divisorInsertion in
`K2-018#eq:k2018-coefficient-compatibility`, on the module source basis. -/
@[simp]
theorem divisorInsertion_intCast (h : d ∣ n) (a : ℤ) :
    divisorInsertion h (a : ZMod d) = (a : ZMod n) * (n / d : ℕ) :=
  ZMod.lift_coe _ _ _

/-- The common-lattice divisorInsertion in
`K2-018#eq:k2018-coefficient-compatibility` is injective at positive levels,
on the module source basis. Positivity of the target excludes `ZMod 0 = Z`. -/
theorem divisorInsertion_injective [NeZero n] (h : d ∣ n) :
    Function.Injective (divisorInsertion h) := by
  unfold divisorInsertion
  rw [ZMod.lift_injective]
  intro a ha
  change (a : ZMod n) * (n / d : ℕ) = 0 at ha
  have hq : n / d ≠ 0 := by
    intro hz
    have hn := Nat.mul_div_cancel' h
    rw [hz, mul_zero] at hn
    exact NeZero.ne n hn.symm
  have hn : (n : ℤ) = (d : ℤ) * (n / d : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' h).symm
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd a d).mpr
  have hm : (n : ℤ) ∣ a * (n / d : ℕ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp (by
      rw [Int.cast_mul, Int.cast_natCast]
      exact ha)
  rw [hn] at hm
  exact (mul_dvd_mul_iff_right (by exact_mod_cast hq)).mp hm

/-- Scalar compatibility of common-lattice divisorInsertion and coefficient
reduction in `K2-018#eq:k2018-coefficient-compatibility`, on the module source
basis. This is the algebra that makes divisorInsertion equivariant after reduction. -/
theorem divisorInsertion_reduction_mul (h : d ∣ n) (a : ZMod n) (b : ZMod d) :
    divisorInsertion h ((castHom h (ZMod d)) a * b) = a * divisorInsertion h b := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective b
  rw [map_intCast, ← Int.cast_mul, divisorInsertion_intCast, divisorInsertion_intCast,
    Int.cast_mul, mul_assoc]

/-- The composite of reduction after divisorInsertion multiplies by `n / d`, an
auxiliary coefficient calculation for
`K2-018#eq:k2018-coefficient-compatibility`, on the module source basis.
This statement is distinct from either Bockstein identity. -/
theorem castHom_divisorInsertion (h : d ∣ n) (b : ZMod d) :
    (castHom h (ZMod d)) (divisorInsertion h b) = (n / d : ℕ) * b := by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective b
  rw [divisorInsertion_intCast, map_mul, map_intCast, map_natCast, mul_comm]

/-- The composite of divisorInsertion after reduction multiplies by `n / d`, an
auxiliary coefficient calculation for
`K2-018#eq:k2018-coefficient-compatibility`, on the module source basis. -/
theorem divisorInsertion_reduction (h : d ∣ n) (a : ZMod n) :
    divisorInsertion h ((castHom h (ZMod d)) a) = (n / d : ℕ) * a := by
  have hi : divisorInsertion h 1 = (n / d : ℕ) := by
    simpa using divisorInsertion_intCast h (1 : ℤ)
  simpa [hi, mul_comm] using divisorInsertion_reduction_mul h a (1 : ZMod d)
end ZMod
