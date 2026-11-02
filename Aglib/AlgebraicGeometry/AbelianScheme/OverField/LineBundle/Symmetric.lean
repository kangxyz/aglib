/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Multiplication
/-!
# Symmetric and antisymmetric multiplication pullback

The symmetric formula is `[n]^* L = L^(n²)` on the original Picard group and
on actual line bundles. The antisymmetric formula is `[n]^* L = L^n`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.LineBundleCube

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

attribute [local instance] Over.cartesianMonoidalCategory

private theorem choose_two_sum (n : ℕ) : (n + 1).choose 2 + n.choose 2 = n ^ 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.choose_succ_succ' (n + 1) 1, Nat.choose_one_right]
    calc
      n + 1 + (n + 1).choose 2 + (n + 1).choose 2 =
          ((n + 1).choose 2 + n.choose 2) + (2 * n + 1) := by
        have hc : (n + 1).choose 2 = n + n.choose 2 := by
          simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' n 1
        omega
      _ = (n + 1) ^ 2 := by
        rw [ih]
        simp only [pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsHProjective G.hom] [GeometricallyIntegral G.hom]

/-- Symmetric classes have the original square-exponent multiplication law. -/
theorem pullbackClass_multiplication_of_symmetric (a : PicardGroup G.left)
    (ha : pullbackClass ((𝟙 G)⁻¹).left a = a) (n : ℕ) :
    pullbackClass ((𝟙 G) ^ n).left a = n ^ 2 • a := by
  rw [pullbackClass_multiplication_choose, ha, ← add_nsmul, choose_two_sum]

/-- Antisymmetric classes have the original linear-exponent multiplication law. -/
theorem pullbackClass_multiplication_of_antisymmetric (a : PicardGroup G.left)
    (ha : pullbackClass ((𝟙 G)⁻¹).left a = -a) (n : ℕ) :
    pullbackClass ((𝟙 G) ^ n).left a = n • a := by
  rw [pullbackClass_multiplication_choose, ha, smul_neg,
    Nat.choose_succ_succ' n 1, Nat.choose_one_right, add_nsmul]
  abel

/-- The symmetric multiplication law between the original actual bundles. -/
theorem nonempty_multiplicationPullbackIso_of_symmetric (L : LineBundle G.left)
    (hL : pullbackClass ((𝟙 G)⁻¹).left (classOf _ L) = classOf _ L) (n : ℕ) :
    Nonempty ((pullbackLineBundle ((𝟙 G) ^ n).left L).val ≅
      (tensorPowerLineBundle G.left L (n ^ 2)).val) := by
  apply (class_eq_iff _ _ _).mp
  change classOf G.left (pullbackLineBundle ((𝟙 G) ^ n).left L) =
    classOf G.left (tensorPowerLineBundle G.left L (n ^ 2))
  rw [← pullbackClass_classOf, classOf_tensorPower]
  exact pullbackClass_multiplication_of_symmetric G (classOf _ L) hL n

end AlgebraicGeometry.Scheme.Group.LineBundleCube
