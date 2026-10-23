/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Data.Int.GCD

/-! # Coprime scalar inversion on an annihilated object

The inverse is an integer multiple of the actual identity, from Bezout's
identity. No change of coefficient category or scalar structure is needed.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Preadditive

universe c h

variable {C : Type c} [Category.{h} C] [Preadditive C]

/-- A scalar prime to an annihilator acts invertibly on the original object. -/
theorem isIso_nsmul_id_of_coprime (A : C) (n p : ℕ) (hcop : n.Coprime p)
    (hp : p • 𝟙 A = 0) : IsIso (n • 𝟙 A) := by
  have hp' : (p : ℤ) • 𝟙 A = 0 := by simpa only [natCast_zsmul] using hp
  have hb : (n : ℤ) * n.gcdA p + (p : ℤ) * n.gcdB p = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
    rfl
  have hs : ((n : ℤ) * n.gcdA p) • 𝟙 A = 𝟙 A := by
    have h := congrArg (fun z : ℤ => z • 𝟙 A) hb
    rw [add_smul, mul_comm (p : ℤ) (n.gcdB p),
      mul_smul (n.gcdB p) (p : ℤ), hp', smul_zero, add_zero, one_smul] at h
    exact h
  refine ⟨⟨n.gcdA p • 𝟙 A, ?_, ?_⟩⟩
  · rw [← natCast_zsmul (𝟙 A) n]
    rw [zsmul_comp, comp_zsmul, Category.id_comp, ← mul_smul]
    exact hs
  · rw [← natCast_zsmul (𝟙 A) n]
    rw [zsmul_comp, comp_zsmul, Category.id_comp, ← mul_smul, mul_comm]
    exact hs

end CategoryTheory.Preadditive
