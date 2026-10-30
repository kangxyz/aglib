/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.ZMod.Reduction

/-!
# Raised-level reduction boundaries

The modulus-zero arithmetic boundary, a composite higher level, and the
failure of cancellation at a fixed level are checked on the original objects.
-/

@[expose] public section

example {d a : ℕ} (hd : 0 < d) (h : 0 ^ (d + 1) ∣ d * a) : a = 0 := by
  simpa only [zero_dvd_iff] using Nat.dvd_of_pow_succ_dvd_mul (n := 0) hd h

example (x : ZMod (4 ^ 3)) (hx : 2 • x = 0) :
    ZMod.castHom (dvd_pow_self 4 (by decide : 3 ≠ 0)) (ZMod 4) x = 0 :=
  ZMod.castHom_eq_zero_of_nsmul_eq_zero_pow_succ (n := 4) (d := 2)
    (by decide) (by decide) x hx

example (d : ℕ) (x : ZMod (1 ^ (d + 1))) :
    ZMod.castHom (dvd_pow_self 1 (Nat.succ_ne_zero d)) (ZMod 1) x = 0 :=
  Subsingleton.elim _ _

example : 2 • (2 : ZMod 4) = 0 ∧ (2 : ZMod 4) ≠ 0 := by decide

/-- info: 'Nat.dvd_of_pow_succ_dvd_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Nat.dvd_of_pow_succ_dvd_mul

/--
info: 'ZMod.castHom_eq_zero_of_nsmul_eq_zero_pow_succ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.castHom_eq_zero_of_nsmul_eq_zero_pow_succ
