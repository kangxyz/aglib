/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.Algebra.Homology.TotalComplexSymmetry
/-!
# Signs for first-quadrant cochain totalization

The native total differential is the horizontal differential plus `(-1)^p`
times the vertical differential in bidegree `(p,q)`. The native flip
isomorphism multiplies that summand by `(-1)^(p*q)`.

Extraction source: `R5Lab.CategoryTheory.Homology.FirstQuadrantSigns` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

namespace ComplexShape

/-- The usual cochain signs on nonnegative degrees. -/
instance upNatTensorSigns : (ComplexShape.up ℕ).TensorSigns where
  ε' := ComplexShape.TensorSigns.ε' (ComplexShape.down ℕ)
  rel_add p q r (h : p + 1 = q) := by change p + r + 1 = q + r; omega
  add_rel p q r (h : p + 1 = q) := by change r + p + 1 = r + q; omega
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ) ^ (p + 1) = -(-1 : ℤˣ) ^ p
    rw [pow_add, pow_one, mul_neg, mul_one]

@[simp]
theorem upNat_ε (p : ℕ) : (ComplexShape.up ℕ).ε p = (-1 : ℤˣ) ^ p := rfl

@[simp]
theorem upNat_ε₁ (p q : ℕ) :
    ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (p, q) = 1 := rfl

@[simp]
theorem upNat_ε₂ (p q : ℕ) :
    ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (p, q) = (-1 : ℤˣ) ^ p := rfl

/-- The Koszul sign for interchanging the two nonnegative cochain degrees. -/
instance upNatTotalComplexShapeSymmetry :
    TotalComplexShapeSymmetry (.up ℕ) (.up ℕ) (.up ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p _ rfl q
    change (-1 : ℤˣ) ^ (p * q) * 1 =
      (-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ ((p + 1) * q)
    rw [mul_one, add_mul, one_mul, pow_add, mul_left_comm,
      Int.units_mul_self, mul_one]
  σ_ε₂ := by
    rintro p q _ rfl
    change (-1 : ℤˣ) ^ (p * q) * (-1 : ℤˣ) ^ p =
      1 * (-1 : ℤˣ) ^ (p * (q + 1))
    rw [one_mul, mul_add, mul_one, pow_add]

@[simp]
theorem upNat_σ (p q : ℕ) :
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) p q = (-1 : ℤˣ) ^ (p * q) := rfl

instance upNatTotalComplexShapeSymmetrySymmetry :
    TotalComplexShapeSymmetrySymmetry (.up ℕ) (.up ℕ) (.up ℕ) where
  σ_symm p q := by simp [Nat.mul_comm]

end ComplexShape
