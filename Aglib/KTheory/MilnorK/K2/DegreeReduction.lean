/-
Copyright (c) 2026 Motivic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.Symbols

/-!
# Symbol identities for degree reduction

These identities express the field-symbol algebra used when cancelling the
leading terms of two polynomial representatives. The nonzero remainder case
is derived directly from the Steinberg relation for `l * a / c` and `e / c`;
the zero remainder case follows from bilinearity and the diagonal identity.
No assertion about polynomial degree, a filtration, or generation is assumed.
-/

@[expose] public section

namespace MilnorK.K2

variable {K : Type*} [Field K]

/-- A nonzero remainder `e = c - l * a` gives the symbol relation used for
leading-term cancellation. -/
theorem symbol_sub_mul_reduction (a c l e : Kˣ)
    (he : (e : K) = (c : K) - (l : K) * (a : K)) :
    symbol a c = symbol a e - symbol c e + symbol l e - symbol l c + symbol c c := by
  have hstein : symbol (l * a / c) (e / c) = 0 := by
    apply steinberg
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    rw [← add_div, he]
    convert div_self c.ne_zero using 1
    ring
  simp only [symbol_div_left, symbol_div_right, symbol_mul_left] at hstein
  calc
    symbol a c =
        (symbol a e - symbol c e + symbol l e - symbol l c + symbol c c) -
          (symbol l e + symbol a e - symbol c e -
            (symbol l c + symbol a c - symbol c c)) := by abel
    _ = _ := by rw [hstein, sub_zero]

/-- If the remainder vanishes, bilinearity reduces the symbol to the
leading coefficient and the sign. -/
theorem symbol_eq_mul_reduction (a c l : Kˣ)
    (hc : (c : K) = (l : K) * (a : K)) :
    symbol a c = symbol a l + symbol a (-1) := by
  have hc' : c = l * a := Units.ext hc
  rw [hc', symbol_mul_right, symbol_self]

end MilnorK.K2
