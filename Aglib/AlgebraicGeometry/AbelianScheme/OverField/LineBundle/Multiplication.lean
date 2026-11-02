/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Cube
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Multiplication pullback of actual line bundles

The original multiplication map is `(𝟙 G)^n`. The cube identity gives its
second-difference recurrence, and hence the usual binomial-coefficient formula.
The tensor-power statement uses the same actual `LineBundle`, tensor powers,
dual/inversion pullback and class quotient. Level zero and level one are
included. Projectivity and geometric integrality remain explicit. Field
flatness is supplied natively.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.LineBundleCube

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

attribute [local instance] Over.cartesianMonoidalCategory

private theorem quadraticSequence_formula {A : Type*} [AddCommGroup A]
    (s : ℕ → A) (a b : A) (h₀ : s 0 = 0) (h₁ : s 1 = a)
    (hrec : ∀ n, s (n + 2) + s n = s (n + 1) + s (n + 1) + a + b) (n : ℕ) :
    s n = (n + 1).choose 2 • a + n.choose 2 • b := by
  have hpair : ∀ n, s n = (n + 1).choose 2 • a + n.choose 2 • b ∧
      s (n + 1) - s n = (n + 1) • a + n • b := by
    intro n
    induction n with
    | zero => simp [h₀, h₁]
    | succ n ih =>
      have hs : s (n + 1) = s n + ((n + 1) • a + n • b) := by
        exact (sub_eq_iff_eq_add.mp ih.2).trans (add_comm _ _)
      constructor
      · rw [hs, ih.1, Nat.choose_succ_succ' (n + 1) 1, Nat.choose_one_right,
          Nat.choose_succ_succ' n 1, Nat.choose_one_right]
        simp only [add_nsmul]
        abel
      · change s (n + 2) - s (n + 1) = (n + 2) • a + (n + 1) • b
        have hs₂ := eq_sub_iff_add_eq.mpr (hrec n)
        calc
          s (n + 2) - s (n + 1) = (s (n + 1) - s n) + a + b := by
            rw [hs₂]
            abel
          _ = (n + 2) • a + (n + 1) • b := by
            rw [ih.2]
            simp only [show n + 2 = (n + 1) + 1 from rfl, add_nsmul, one_nsmul]
            abel
  exact (hpair n).1

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsHProjective G.hom] [GeometricallyIntegral G.hom]

/-- The second-difference identity for the original multiplication pullbacks. -/
theorem multiplication_pullback_recurrence (a : PicardGroup G.left) (n : ℕ) :
    pullbackHom ((𝟙 G) ^ (n + 2)).left a + pullbackHom ((𝟙 G) ^ n).left a =
      pullbackHom ((𝟙 G) ^ (n + 1)).left a +
        pullbackHom ((𝟙 G) ^ (n + 1)).left a + a + pullbackHom ((𝟙 G)⁻¹).left a := by
  have hc := cubeClass_eq_zero G ((𝟙 G) ^ (n + 1)) (𝟙 G) ((𝟙 G)⁻¹) a
  have hplus : (𝟙 G) ^ (n + 1) * 𝟙 G = (𝟙 G) ^ (n + 2) :=
    (pow_succ (𝟙 G) (n + 1)).symm
  have hminus : (𝟙 G) ^ (n + 1) * (𝟙 G)⁻¹ = (𝟙 G) ^ n := by
    rw [pow_succ, _root_.mul_assoc, mul_inv_cancel, _root_.mul_one]
  have htotal : ((𝟙 G) ^ (n + 1) * 𝟙 G) * (𝟙 G)⁻¹ =
      (𝟙 G) ^ (n + 1) := by rw [_root_.mul_assoc, mul_inv_cancel, _root_.mul_one]
  unfold cubeClass at hc
  rw [htotal, hplus, hminus, mul_inv_cancel] at hc
  simp only [pullbackHom_apply, pullbackClass_one, Over.id_left,
    pullbackClass_id, sub_zero] at hc
  simp only [pullbackHom_apply]
  apply sub_eq_zero.mp
  have hneg := congrArg Neg.neg hc
  simp only [neg_zero] at hneg
  convert hneg using 1
  abel

/-- The multiplication pullback formula, including zero and one, on the
original Picard group. The coefficients are natural binomial coefficients. -/
theorem pullbackClass_multiplication_choose (a : PicardGroup G.left) (n : ℕ) :
    pullbackClass ((𝟙 G) ^ n).left a =
      (n + 1).choose 2 • a + n.choose 2 • pullbackClass ((𝟙 G)⁻¹).left a := by
  apply quadraticSequence_formula (fun n => pullbackHom ((𝟙 G) ^ n).left a) a
    (pullbackHom ((𝟙 G)⁻¹).left a)
  · simp only [pow_zero, pullbackHom_apply, pullbackClass_one]
  · simp only [pow_one, pullbackHom_apply, Over.id_left, pullbackClass_id]
  · exact multiplication_pullback_recurrence G a

/-- The usual `n(n+1)/2`, `n(n-1)/2` form of the same original-map identity. -/
theorem pullbackClass_multiplication (a : PicardGroup G.left) (n : ℕ) :
    pullbackClass ((𝟙 G) ^ n).left a =
      (n * (n + 1) / 2) • a + (n * (n - 1) / 2) • pullbackClass ((𝟙 G)⁻¹).left a := by
  simpa only [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm] using
    pullbackClass_multiplication_choose G a n

/-- The multiplication formula as an isomorphism between the actual pulled
back bundle and the actual tensor powers. -/
theorem nonempty_multiplicationPullbackIso (L : LineBundle G.left) (n : ℕ) :
    Nonempty ((pullbackLineBundle ((𝟙 G) ^ n).left L).val ≅
      (tensorLineBundle G.left (tensorPowerLineBundle G.left L (n * (n + 1) / 2))
        (tensorPowerLineBundle G.left (pullbackLineBundle ((𝟙 G)⁻¹).left L)
          (n * (n - 1) / 2))).val) := by
  apply (class_eq_iff _ _ _).mp
  change classOf G.left (pullbackLineBundle ((𝟙 G) ^ n).left L) =
    classOf G.left (tensorLineBundle G.left
      (tensorPowerLineBundle G.left L (n * (n + 1) / 2))
      (tensorPowerLineBundle G.left (pullbackLineBundle ((𝟙 G)⁻¹).left L)
        (n * (n - 1) / 2)))
  rw [← pullbackClass_classOf, classOf_tensor, classOf_tensorPower, classOf_tensorPower,
    ← pullbackClass_classOf]
  exact pullbackClass_multiplication G (classOf _ L) n

end AlgebraicGeometry.Scheme.Group.LineBundleCube
