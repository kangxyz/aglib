/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.Residue

/-!
# Symbol identities in the actual degree-three Milnor quotient

Fixing the last unit gives an integer-linear map from the original `K2 K`
quotient to `K3 K`: its Steinberg descent is the first-adjacent defining
relation of `K3 K`. This transports the proved degree-two sign laws to the
first pair. The second pair inherits them directly from the nested tensor.

The Euclidean identity is proved from Steinberg on `(p/q,r/q)`, with its
repeated-entry term retained as `{q,-1}`. No norm, polynomial exactness,
abstract graded algebra, or additional symbol relation is assumed.
-/

@[expose] public section

namespace MilnorK.K3

open MilnorK.K2

variable {K : Type*} [Field K]

/-- Fixing the last unit descends through the original K₂ tensor quotient. -/
def symbol3FixedLast (c : Kˣ) : MilnorK.K2.Group K →ₗ[ℤ] Group K :=
  (liftSymbols {
    toFun := fun a b => symbol3 a b c
    mul_left := fun a a' b => symbol3_mul_left a a' b c
    mul_right := fun a b b' => symbol3_mul_middle a b b' c
    steinberg := fun a b hab => symbol3_steinberg_left a b c hab
  }).toIntLinearMap

/-- The fixed-last linear map takes the literal three-entry symbol value. -/
@[simp] theorem symbol3FixedLast_symbol (c a b : Kˣ) :
    symbol3FixedLast c (symbol a b) = symbol3 a b c := rfl

/-- The first adjacent pair is skew, by the actual degree-two quotient lift. -/
theorem symbol3_skew_left (a b c : Kˣ) :
    symbol3 a b c = -symbol3 b a c := by
  have h := congrArg (symbol3FixedLast c) (symbol_skew a b)
  simpa only [symbol3FixedLast_symbol, map_neg] using h

/-- The last adjacent pair is skew in the nested degree-two tensor factor. -/
theorem symbol3_skew_right (a b c : Kˣ) :
    symbol3 a b c = -symbol3 a c b := by
  simp only [symbol3, symbol_skew b c, TensorProduct.tmul_neg, map_neg]

/-- Moving the last entry to the first has positive sign in degree three. -/
theorem symbol3_cyclic (a b c : Kˣ) :
    symbol3 a b c = symbol3 c a b := by
  rw [symbol3_skew_right a b c, symbol3_skew_left a c b, neg_neg]

/-- The inverse cyclic permutation also has positive sign. -/
theorem symbol3_cyclic_left (a b c : Kˣ) :
    symbol3 a b c = symbol3 b c a := by
  rw [symbol3_skew_left a b c, symbol3_skew_right b a c, neg_neg]

/-- A unit and its negative in the first adjacent pair give zero. -/
theorem symbol3_self_neg_left (a c : Kˣ) : symbol3 a (-a) c = 0 := by
  have h := congrArg (symbol3FixedLast c) (symbol_self_neg a)
  simpa only [symbol3FixedLast_symbol, map_zero] using h

/-- A unit and its negative in the last adjacent pair give zero. -/
theorem symbol3_self_neg_right (a b : Kˣ) : symbol3 a b (-b) = 0 := by
  simp only [symbol3, symbol_self_neg, TensorProduct.tmul_zero, map_zero]

/-- A repeated first pair retains the sign unit rather than being forced to zero. -/
theorem symbol3_self_left (a c : Kˣ) : symbol3 a a c = symbol3 a (-1) c := by
  have h := congrArg (symbol3FixedLast c) (symbol_self a)
  simpa only [symbol3FixedLast_symbol] using h

/-- A repeated last pair retains the sign unit in the original K₂ factor. -/
theorem symbol3_self_right (a b : Kˣ) : symbol3 a b b = symbol3 a b (-1) := by
  simp only [symbol3, symbol_self]

/-- A first entry equal to one vanishes. -/
@[simp] theorem symbol3_one_left (b c : Kˣ) : symbol3 1 b c = 0 := by
  have h := congrArg (symbol3FixedLast c) (symbol_one_left b)
  simpa only [symbol3FixedLast_symbol, map_zero] using h

/-- A middle entry equal to one vanishes. -/
@[simp] theorem symbol3_one_middle (a c : Kˣ) : symbol3 a 1 c = 0 := by
  simp only [symbol3, symbol_one_left, TensorProduct.tmul_zero, map_zero]

/-- A last entry equal to one vanishes. -/
@[simp] theorem symbol3_one_right (a b : Kˣ) : symbol3 a b 1 = 0 := by
  simp only [symbol3, symbol_one_right, TensorProduct.tmul_zero, map_zero]

/-- Inverting the first entry negates the symbol. -/
@[simp] theorem symbol3_inv_left (a b c : Kˣ) :
    symbol3 a⁻¹ b c = -symbol3 a b c := by
  have h := congrArg (symbol3FixedLast c) (symbol_inv_left a b)
  simpa only [symbol3FixedLast_symbol, map_neg] using h

/-- Inverting the middle entry negates the symbol. -/
@[simp] theorem symbol3_inv_middle (a b c : Kˣ) :
    symbol3 a b⁻¹ c = -symbol3 a b c := by
  have h := congrArg (symbol3FixedLast c) (symbol_inv_right a b)
  simpa only [symbol3FixedLast_symbol, map_neg] using h

/-- Inverting the last entry negates the symbol. -/
@[simp] theorem symbol3_inv_right (a b c : Kˣ) :
    symbol3 a b c⁻¹ = -symbol3 a b c := by
  simp only [symbol3, symbol_inv_right, TensorProduct.tmul_neg, map_neg]

/-- Division in the first entry expands as subtraction. -/
theorem symbol3_div_left (a a' b c : Kˣ) :
    symbol3 (a / a') b c = symbol3 a b c - symbol3 a' b c := by
  rw [div_eq_mul_inv, symbol3_mul_left, symbol3_inv_left, sub_eq_add_neg]

/-- Division in the middle entry expands as subtraction. -/
theorem symbol3_div_middle (a b b' c : Kˣ) :
    symbol3 a (b / b') c = symbol3 a b c - symbol3 a b' c := by
  rw [div_eq_mul_inv, symbol3_mul_middle, symbol3_inv_middle, sub_eq_add_neg]

/-- Division in the last entry expands as subtraction. -/
theorem symbol3_div_right (a b c c' : Kˣ) :
    symbol3 a b (c / c') = symbol3 a b c - symbol3 a b c' := by
  rw [div_eq_mul_inv, symbol3_mul_right, symbol3_inv_right, sub_eq_add_neg]

/-- Steinberg on the normalized sum gives the sign-correct degree-two identity. -/
private theorem symbol_euclidean (p q r : Kˣ) (h : (p : K) + (r : K) = q) :
    symbol p q = symbol p r - symbol q r + symbol q (-1) := by
  have hsum : ((p / q : Kˣ) : K) + ((r / q : Kˣ) : K) = 1 := by
    simp only [Units.val_div_eq_div_val]
    rw [← add_div, h, div_self q.ne_zero]
  have hs := steinberg (p / q) (r / q) hsum
  rw [symbol_div_left, symbol_div_right, symbol_div_right, symbol_self] at hs
  calc
    symbol p q = (symbol p r - symbol q r + symbol q (-1)) -
        ((symbol p r - symbol p q) - (symbol q r - symbol q (-1))) := by abel
    _ = symbol p r - symbol q r + symbol q (-1) := by rw [hs, sub_zero]

/-- The first-pair Euclidean identity in the actual K₃ quotient, including its sign term. -/
theorem symbol3_euclidean (p q r b : Kˣ) (h : (p : K) + (r : K) = q) :
    symbol3 p q b = symbol3 p r b - symbol3 q r b + symbol3 q (-1) b := by
  have he := congrArg (symbol3FixedLast b) (symbol_euclidean p q r h)
  simpa only [symbol3FixedLast_symbol, map_add, map_sub] using he

end MilnorK.K3
