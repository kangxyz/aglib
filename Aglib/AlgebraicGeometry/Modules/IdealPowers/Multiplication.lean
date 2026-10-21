/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Basic

/-! # Homogeneous multiplication on actual ideal-power coefficients -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) (F : X.Modules)

/-- Multiplication on scalar presentations, for a scalar taking one ideal into another. -/
def idealEvaluationMul {J K : Ideal A} (a : A) (ha : ∀ b ∈ J, a * b ∈ K) :
    (∐ fun _ : J => F) ⟶ (∐ fun _ : K => F) :=
  Sigma.desc fun b => Sigma.ι (fun _ : K => F) ⟨a * b, ha b b.property⟩

@[reassoc]
theorem idealEvaluationMul_evaluation {J K : Ideal A} (a : A)
    (ha : ∀ b ∈ J, a * b ∈ K) :
    idealEvaluationMul X F a ha ≫ idealEvaluation X α F K =
      idealEvaluation X α F J ≫ globalScalarEndomorphism X F (α a) := by
  apply Sigma.hom_ext
  intro b
  simp only [idealEvaluationMul, idealEvaluation, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
  change ((globalScalarCenter X) (α (a * b))).app F =
    ((globalScalarCenter X) (α b)).app F ≫ ((globalScalarCenter X) (α a)).app F
  rw [map_mul, map_mul, CatCenter.mul_app']

/-- Multiplication by a scalar taking `J` into `K`, on the actual image coefficients. -/
def idealMultipleMul {J K : Ideal A} (a : A) (ha : ∀ b ∈ J, a * b ∈ K) :
    idealMultiple X α F J ⟶ idealMultiple X α F K :=
  image.map (Arrow.homMk' (f := idealEvaluation X α F J)
    (g := idealEvaluation X α F K) (idealEvaluationMul X F a ha)
    (globalScalarEndomorphism X F (α a))
    (idealEvaluationMul_evaluation X α F a ha))

@[reassoc (attr := simp)]
theorem idealMultipleMul_ι {J K : Ideal A} (a : A)
    (ha : ∀ b ∈ J, a * b ∈ K) :
    idealMultipleMul X α F a ha ≫ idealMultipleι X α F K =
      idealMultipleι X α F J ≫ globalScalarEndomorphism X F (α a) := by
  dsimp only [idealMultipleMul, idealMultipleι]
  exact image.map_ι _

/-- Multiplication is compatible with inclusions in both source and target ideals. -/
theorem idealMultipleMul_naturality {J J' K K' : Ideal A}
    (hJ : J ≤ J') (hK : K ≤ K') (a : A)
    (ha : ∀ b ∈ J, a * b ∈ K) (ha' : ∀ b ∈ J', a * b ∈ K') :
    idealMultipleMap X α F hJ ≫ idealMultipleMul X α F a ha' =
      idealMultipleMul X α F a ha ≫ idealMultipleMap X α F hK := by
  apply (cancel_mono (idealMultipleι X α F K')).mp
  simp only [Category.assoc, idealMultipleMul_ι, idealMultipleMap_ι,
    idealMultipleMap_ι_assoc]

/-- Composition of ideal multiplications retains the product scalar. -/
theorem idealMultipleMul_comp {J K L : Ideal A} (a b : A)
    (ha : ∀ x ∈ J, a * x ∈ K) (hb : ∀ x ∈ K, b * x ∈ L) :
    idealMultipleMul X α F a ha ≫ idealMultipleMul X α F b hb =
      idealMultipleMul X α F (b * a)
        (fun x hx => by rw [mul_assoc]; exact hb _ (ha x hx)) := by
  apply (cancel_mono (idealMultipleι X α F L)).mp
  simp only [Category.assoc, idealMultipleMul_ι, idealMultipleMul_ι_assoc]
  simp only [globalScalarEndomorphism, map_mul, CatCenter.mul_app']

/-- The unit scalar acts as the identity on every actual ideal multiple. -/
theorem idealMultipleMul_one (J : Ideal A) :
    idealMultipleMul X α F 1 (fun x hx => by simpa using hx : ∀ x ∈ J, 1 * x ∈ J) =
      𝟙 (idealMultiple X α F J) := by
  apply (cancel_mono (idealMultipleι X α F J)).mp
  simp [globalScalarEndomorphism]

/-- The degree-raising multiplication associated to an element of `Iʳ`. -/
def idealPowerMul (I : Ideal A) (r n : ℕ) (a : ↥(I ^ r)) :
    idealPower X α F I n ⟶ idealPower X α F I (r + n) :=
  idealMultipleMul X α F a fun b hb => by
    rw [pow_add]
    exact Ideal.mul_mem_mul a.property hb

/-- Lowering the result of homogeneous multiplication gives ordinary scalar multiplication.
This is the action-degree compatibility, not merely compatibility in the module degree. -/
theorem idealPowerMul_transition (I : Ideal A) (r n : ℕ) (a : ↥(I ^ r)) :
    idealPowerMul X α F I r n a ≫ idealPowerMap X α F I (Nat.le_add_left n r) =
      globalScalarEndomorphism X (idealPower X α F I n) (α a) := by
  apply (cancel_mono (idealMultipleι X α F (I ^ n))).mp
  rw [Category.assoc, idealMultipleMap_ι]
  change idealMultipleMul X α F _ _ ≫ idealMultipleι X α F (I ^ (r + n)) = _
  rw [idealMultipleMul_ι]
  exact (globalScalarCenter X (α a)).naturality _

end AlgebraicGeometry.Scheme.Modules
