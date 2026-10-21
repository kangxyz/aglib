/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.QuotientMultiplication

/-!
# Scalar maps on kernels between original quotient levels

These finite-stage maps are defined before any completion or algebraization.
They provide homogeneous multiplication on successive pieces by using a common
coefficient at a sufficiently high level of the original formal system.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable (X : Scheme.{u}) {A : Type u} [CommRing A]
  (α : A →+* Γ(X, ⊤)) (F : X.Modules)

/-- Scalar multiplication commutes with both original quotient reductions. -/
@[reassoc]
theorem idealQuotientMul_map {J J' K K' : Ideal A}
    (hJ : J ≤ J') (hK : K ≤ K') (a : A)
    (ha : ∀ b ∈ J, a * b ∈ K) (ha' : ∀ b ∈ J', a * b ∈ K') :
    idealQuotientMul X α F a ha ≫ idealQuotientMap X α F hK =
      idealQuotientMap X α F hJ ≫ idealQuotientMul X α F a ha' := by
  apply (cancel_epi (idealQuotientπ X α F J)).mp
  simp

/-- The layer between two actual quotient levels. -/
abbrev idealQuotientLayer {J J' : Ideal A} (h : J ≤ J') : X.Modules :=
  kernel (idealQuotientMap X α F h)

/-- The original scalar map on a layer, induced from its original quotient square. -/
def idealQuotientLayerMul {J J' K K' : Ideal A}
    (hJ : J ≤ J') (hK : K ≤ K') (a : A)
    (ha : ∀ b ∈ J, a * b ∈ K) (ha' : ∀ b ∈ J', a * b ∈ K') :
    idealQuotientLayer X α F hJ ⟶ idealQuotientLayer X α F hK :=
  kernel.map (idealQuotientMap X α F hJ) (idealQuotientMap X α F hK)
    (idealQuotientMul X α F a ha) (idealQuotientMul X α F a ha')
    (idealQuotientMul_map X α F hJ hK a ha ha').symm

/-- The layer action retains multiplication on the original upper quotient. -/
@[reassoc (attr := simp)]
theorem idealQuotientLayerMul_ι {J J' K K' : Ideal A}
    (hJ : J ≤ J') (hK : K ≤ K') (a : A)
    (ha : ∀ b ∈ J, a * b ∈ K) (ha' : ∀ b ∈ J', a * b ∈ K') :
    idealQuotientLayerMul X α F hJ hK a ha ha' ≫
      kernel.ι (idealQuotientMap X α F hK) =
    kernel.ι (idealQuotientMap X α F hJ) ≫ idealQuotientMul X α F a ha := by
  simp [idealQuotientLayerMul]

/-- Homogeneous scalar multiplication between successive quotient kernels. -/
def idealPowerQuotientLayerMul (I : Ideal A) (r n : ℕ) (a : ↥(I ^ r)) :
    idealQuotientLayer X α F (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n) ⟶
      idealQuotientLayer X α F
        (Ideal.pow_le_pow_right (Nat.le_succ (r + n)) : I ^ (r + n + 1) ≤ I ^ (r + n)) :=
  idealQuotientLayerMul X α F _ _ a
    (fun b hb => by
      rw [show r + n + 1 = r + (n + 1) from Nat.add_assoc r n 1, pow_add]
      exact Ideal.mul_mem_mul a.property hb)
    (fun b hb => by
      rw [pow_add]
      exact Ideal.mul_mem_mul a.property hb)

end AlgebraicGeometry.Scheme.Modules
