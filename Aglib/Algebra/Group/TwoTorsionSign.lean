/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Integer scalar identities for elements killed by two

The scalar-correction identity is extracted from
`lean/R5Lab/Aglib/RingTheory/DiscreteValuationRing/Ramification.lean`:190–210 at R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`. The parity helper is the generic additive
argument already present as `MilnorK.K2.square_sub_smul_eq_zero` in native
`Aglib.KTheory.MilnorK.K2.Residue`; this lower leaf imports no K-theory objects.
-/

@[expose] public section

namespace AddCommGroup

/-- A two-torsion element is annihilated by every integer `m² - m`. -/
theorem square_sub_zsmul_eq_zero {A : Type*} [AddCommGroup A]
    (x : A) (hx : x + x = 0) (m : ℤ) : (m * m - m) • x = 0 := by
  have htwo : (2 : ℤ) • x = 0 := by simpa only [two_smul] using hx
  refine Int.induction_on m ?_ ?_ ?_
  · simp
  · intro z hz
    have heq : ((z : ℤ) + 1) * ((z : ℤ) + 1) - ((z : ℤ) + 1) =
        ((z : ℤ) * (z : ℤ) - (z : ℤ)) + (z : ℤ) * 2 := by ring
    rw [heq, add_zsmul, hz, mul_zsmul, htwo, zsmul_zero, add_zero]
  · intro z hz
    have heq : (-(z : ℤ) - 1) * (-(z : ℤ) - 1) - (-(z : ℤ) - 1) =
        (-(z : ℤ) * -(z : ℤ) - -(z : ℤ)) + (1 + (z : ℤ)) * 2 := by ring
    rw [heq, add_zsmul, hz, mul_zsmul, htwo, zsmul_zero, add_zero]

/-- The exact scalar correction for a two-torsion sign, in an arbitrary additive group. -/
theorem twoTorsion_scalar_correction {A : Type*} [AddCommGroup A]
    (s x y c : A) (hs : s + s = 0) (e m n : ℤ) :
    ((e * m) * (e * n)) • s + (e * n) • (x + m • c) -
        (e * m) • (y + n • c) =
      e • ((m * n) • s + n • x - m • y) := by
  have hsquare := square_sub_zsmul_eq_zero s hs e
  have hsign : ((e * m) * (e * n)) • s = (e * (m * n)) • s := by
    apply sub_eq_zero.mp
    rw [← sub_smul]
    calc
      ((e * m) * (e * n) - e * (m * n)) • s =
          (m * n) • ((e * e - e) • s) := by
            rw [← mul_zsmul]
            congr 1
            ring
      _ = 0 := by rw [hsquare, zsmul_zero]
  rw [hsign]
  simp only [zsmul_add, zsmul_sub, ← mul_zsmul]
  rw [show e * n * m = e * m * n by ring]
  abel

end AddCommGroup
