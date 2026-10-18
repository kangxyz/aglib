/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Henselian

/-!
# Roots of principal units in henselian local rings

If `n > 0` is invertible in a henselian local ring, every element with residue
`1` has an `n`-th root with residue `1`. We lift the simple root `1` of
`X ^ n - C h` and then deduce invertibility of the lift from its residue.
No assumption that the ring is a domain or has characteristic zero is needed.

When the residue field has characteristic zero, every positive exponent is
invertible, giving the corresponding unrestricted positive-exponent consumer.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace HenselianLocalRing.PrincipalRoots

variable {R : Type*} [CommRing R]

section Henselian

variable [HenselianLocalRing R]

/-- Hensel lifting of `1` for `X ^ n - h`, with the prescribed residue. -/
theorem exists_root (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (h : R) (hh : residue R h = 1) :
    ∃ y : R, residue R y = 1 ∧ y ^ n = h := by
  have hroot : (X ^ n - C h).eval (1 : R) ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff]
    simp [hh]
  have hderivative : IsUnit ((X ^ n - C h).derivative.eval (1 : R)) := by
    simpa [derivative_X_pow] using hnunit
  obtain ⟨y, hy, hyres⟩ := HenselianLocalRing.is_henselian
    (X ^ n - C h) (monic_X_pow_sub_C h (Nat.ne_of_gt hn)) 1 hroot hderivative
  refine ⟨y, ?_, ?_⟩
  · rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero] at hyres
    exact hyres
  · simpa only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hy

/-- The root of a principal element is itself a principal unit. -/
theorem exists_unit_root (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (h : R) (hh : residue R h = 1) :
    ∃ y : Rˣ, residue R (y : R) = 1 ∧ (y : R) ^ n = h := by
  obtain ⟨y, hyres, hy⟩ := exists_root n hn hnunit h hh
  have hyunit : IsUnit y := (residue_ne_zero_iff_isUnit y).mp (by
    rw [hyres]
    exact one_ne_zero)
  obtain ⟨u, rfl⟩ := hyunit
  exact ⟨u, hyres, hy⟩

/-- Every principal ring unit has a principal root for every invertible exponent. -/
theorem exists_pow_eq (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (h : Rˣ) (hh : residue R (h : R) = 1) :
    ∃ y : Rˣ, residue R (y : R) = 1 ∧ y ^ n = h := by
  obtain ⟨y, hyres, hy⟩ := exists_unit_root n hn hnunit (h : R) hh
  exact ⟨y, hyres, Units.ext (by simpa only [Units.val_pow_eq_pow_val] using hy)⟩

end Henselian

/-- Residue characteristic zero makes every positive natural exponent invertible. -/
theorem isUnit_natCast_of_residue_charZero [IsLocalRing R] [CharZero (ResidueField R)]
    (n : ℕ) (hn : 0 < n) : IsUnit (n : R) := by
  apply (residue_ne_zero_iff_isUnit (n : R)).mp
  simpa only [map_natCast, Nat.cast_ne_zero] using Nat.ne_of_gt hn

variable [HenselianLocalRing R]

/-- The ring-element form for a henselian local ring of residue characteristic zero. -/
theorem exists_unit_root_of_residue_charZero [CharZero (ResidueField R)]
    (n : ℕ) (hn : 0 < n) (h : R) (hh : residue R h = 1) :
    ∃ y : Rˣ, residue R (y : R) = 1 ∧ (y : R) ^ n = h :=
  exists_unit_root n hn (isUnit_natCast_of_residue_charZero n hn) h hh

/-- Principal units are divisible in a henselian local ring of residue characteristic zero. -/
theorem exists_pow_eq_of_residue_charZero [CharZero (ResidueField R)]
    (n : ℕ) (hn : 0 < n) (h : Rˣ) (hh : residue R (h : R) = 1) :
    ∃ y : Rˣ, residue R (y : R) = 1 ∧ y ^ n = h :=
  exists_pow_eq n hn (isUnit_natCast_of_residue_charZero n hn) h hh

end HenselianLocalRing.PrincipalRoots
