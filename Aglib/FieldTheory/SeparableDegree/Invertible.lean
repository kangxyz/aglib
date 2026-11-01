/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Algebra.Divisibility.Units

/-! # Separability from invertibility of the original finite degree

The inseparable degree is a characteristic power dividing the original degree.
If that degree is invertible in the base field, the inseparable degree is one.
No perfectness or separability hypothesis is used.
-/

@[expose] public noncomputable section

namespace Field

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E]

/-- A finite extension whose actual degree is a unit in the original base
field is separable. The two field universes are independent. -/
theorem isSeparable_of_isUnit_finrank (h : IsUnit (Module.finrank F E : F)) :
    Algebra.IsSeparable F E := by
  have hu : IsUnit (finInsepDegree F E : F) := by
    apply isUnit_of_dvd_unit _ h
    refine ⟨(finSepDegree F E : F), ?_⟩
    rw [← Nat.cast_mul, mul_comm, finSepDegree_mul_finInsepDegree]
  apply (isSeparable_iff_finInsepDegree_eq_one F E).mpr
  obtain ⟨q, hq⟩ := ExpChar.exists F
  let := hq
  obtain ⟨m, hm⟩ := finInsepDegree_eq_pow F E q
  rcases expChar_is_prime_or_one F q with hp | hqone
  · let : CharP F q := (expChar_prime_iff F hp).mp hq
    by_cases hmzero : m = 0
    · simpa only [hmzero, pow_zero] using hm
    · have hz : (finInsepDegree F E : F) = 0 := by
        rw [hm, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hmzero]
      exact False.elim (hu.ne_zero hz)
  · simpa only [hqone, one_pow] using hm

end Field
