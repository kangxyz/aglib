/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalZeroResidue
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalTranslation

/-!
# General rational norm compatibility at linear places

Literal translation transports the proved all-degree zero-place square.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {k : Type*} [Field k] [CharZero k]

local instance {L : Type*} [Field L] (a : L) :
    Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩

/-- The general rational norm commutes with the original linear-place residue. -/
theorem residueAt_linear_rationalFunctionNorm
    (p : MonicIrreducible k) (a : k) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (linearRootEquiv a).toRingHom
      (residueAt (X - C a) n (rationalFunctionNorm (n + 1) p x)) =
      polynomialNorm n p
        (map n (linearRootEquiv (algebraMap k (AdjoinRoot p.val) a)).toRingHom
          (residueAt (X - C (algebraMap k (AdjoinRoot p.val) a)) n x)) := by
  rw [residueAt_linear_eq_residueAt_X_translation a, rationalFunctionNorm_translation,
    residueAt_linear_eq_residueAt_X_translation]
  exact rationalZeroResidue_rationalFunctionNorm p n _

end MilnorK.PolynomialNorm
