/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Reduction of annihilated cyclic coefficients

An element killed by a positive integer `d` at level `n^(d+1)` reduces to zero
at level `n`. No coprimality between `d` and `n` is required. The finite-cover
trace comparison uses this with positive invertible `n`, without introducing
an adic coefficient object.
-/

@[expose] public section

namespace Nat

/-- Raising the level absorbs the part of a positive multiplier supported on
the coefficient modulus. The modulus may also be zero. -/
theorem dvd_of_pow_succ_dvd_mul {n d a : ℕ} (hd : 0 < d)
    (h : n ^ (d + 1) ∣ d * a) : n ∣ a := by
  suffices aux : ∀ m : ℕ, 0 < m → n ^ (m + 1) ∣ m * a → n ∣ a from aux d hd h
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm hmdiv
    let g := Nat.gcd n m
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_right n hm
    by_cases hg : g = 1
    · have hcop : Nat.Coprime n m := hg
      exact hcop.dvd_of_dvd_mul_left
        ((dvd_pow_self n (Nat.succ_ne_zero m)).trans hmdiv)
    · have hg1 : 1 < g := lt_of_le_of_ne (Nat.succ_le_iff.mpr hg0) (Ne.symm hg)
      obtain ⟨q, hq⟩ : g ∣ m := Nat.gcd_dvd_right n m
      have hq0 : 0 < q := by
        apply Nat.pos_of_ne_zero
        intro hz
        apply Nat.ne_of_gt hm
        simpa [hz] using hq
      have hqlt : q < m := by
        rw [hq]
        simpa using Nat.mul_lt_mul_of_pos_right hg1 hq0
      have hgpow : g * n ^ m ∣ n ^ (m + 1) := by
        obtain ⟨b, hb⟩ : g ∣ n := Nat.gcd_dvd_left n m
        refine ⟨b, ?_⟩
        rw [pow_succ, hb]
        ac_rfl
      have hcancel : n ^ m ∣ q * a := by
        apply (Nat.mul_dvd_mul_iff_left hg0).mp
        apply hgpow.trans
        simpa [hq, mul_assoc] using hmdiv
      exact ih q hqlt hq0 ((pow_dvd_pow n (Nat.succ_le_of_lt hqlt)).trans hcancel)

end Nat

namespace ZMod

/-- Canonical level reduction kills elements annihilated by `d` after raising
the original positive modulus to `n^(d+1)`. Composite levels and level one are
included. -/
theorem castHom_eq_zero_of_nsmul_eq_zero_pow_succ {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (x : ZMod (n ^ (d + 1))) (hx : d • x = 0) :
    ZMod.castHom (dvd_pow_self n (Nat.succ_ne_zero d)) (ZMod n) x = 0 := by
  have : NeZero (n ^ (d + 1)) := ⟨pow_ne_zero _ (Nat.ne_of_gt hn)⟩
  have hdiv : n ^ (d + 1) ∣ d * x.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul] using hx
  have hred : (x.val : ZMod n) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_pow_succ_dvd_mul hd hdiv)
  calc
    ZMod.castHom (dvd_pow_self n (Nat.succ_ne_zero d)) (ZMod n) x =
        (x.val : ZMod n) := by
      simpa only [ZMod.castHom_apply] using (ZMod.natCast_val (R := ZMod n) x).symm
    _ = 0 := hred

end ZMod
