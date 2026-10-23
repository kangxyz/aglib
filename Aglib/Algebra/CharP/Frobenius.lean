/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Frobenius

/-!
# Frobenius under a prime-cast equation

The prime-power ring endomorphism needs only the equation `p = 0` in the
commutative semiring. This includes the trivial semiring, for which the exact
characteristic need not be `p`. The underlying function remains the literal
power map in both cases.
-/

@[expose] public noncomputable section

namespace RingHom

variable {R : Type*} [CommSemiring R]

/-- The original prime-power map, including in a trivial semiring. -/
def frobeniusOfPrimeCastEqZero (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.ne_zero
  map_add' x y := by
    rcases subsingleton_or_nontrivial R with h | h
    · let := h
      exact Subsingleton.elim _ _
    · let := h
      let : Fact p.Prime := ⟨hp⟩
      let : CharP R p := (CharP.charP_iff_prime_eq_zero hp).2 hR
      exact (frobenius R p).map_add x y

@[simp] theorem frobeniusOfPrimeCastEqZero_apply
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (x : R) :
    frobeniusOfPrimeCastEqZero p hp hR x = x ^ p := rfl

end RingHom
