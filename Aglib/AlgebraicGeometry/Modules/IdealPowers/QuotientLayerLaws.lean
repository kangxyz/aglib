/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.QuotientLayers

/-! # Scalar representative independence for finite quotient layers -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable (X : Scheme.{u}) {A : Type u} [CommRing A]
  (α : A →+* Γ(X, ⊤)) (F : X.Modules)

/-- If a scalar carries the larger source ideal into the smaller target ideal,
its map on the original quotient layer is zero. -/
theorem idealQuotientLayerMul_eq_zero {J J' K K' : Ideal A}
    (hJ : J ≤ J') (hK : K ≤ K') (a : A)
    (ha : ∀ b ∈ J, a * b ∈ K) (ha' : ∀ b ∈ J', a * b ∈ K')
    (hstrong : ∀ b ∈ J', a * b ∈ K) :
    idealQuotientLayerMul X α F hJ hK a ha ha' = 0 := by
  have hfactor : idealQuotientMul X α F a ha =
      idealQuotientMap X α F hJ ≫ idealQuotientMul X α F a hstrong := by
    apply (cancel_epi (idealQuotientπ X α F J)).mp
    simp
  apply (cancel_mono (kernel.ι (idealQuotientMap X α F hK))).mp
  rw [idealQuotientLayerMul_ι, hfactor, ← Category.assoc, kernel.condition,
    zero_comp, zero_comp]

/-- The homogeneous degree-r action kills every scalar in the next ideal power.
This is the required representative-independence vanishing, before completion. -/
theorem idealPowerQuotientLayerMul_eq_zero (I : Ideal A) (r n : ℕ)
    (a : ↥(I ^ r)) (ha : (a : A) ∈ I ^ (r + 1)) :
    idealPowerQuotientLayerMul X α F I r n a = 0 := by
  apply idealQuotientLayerMul_eq_zero
  intro b hb
  rw [show r + n + 1 = (r + 1) + n by omega, pow_add]
  exact Ideal.mul_mem_mul ha hb

/-- Addition of scalar maps is addition on the actual kernel layer. -/
theorem idealQuotientLayerMul_add {J J' K K' : Ideal A}
    (hJ : J ≤ J') (hK : K ≤ K') (a b : A)
    (ha : ∀ x ∈ J, a * x ∈ K) (ha' : ∀ x ∈ J', a * x ∈ K')
    (hb : ∀ x ∈ J, b * x ∈ K) (hb' : ∀ x ∈ J', b * x ∈ K') :
    idealQuotientLayerMul X α F hJ hK (a + b)
      (fun x hx => by rw [add_mul]; exact K.add_mem (ha x hx) (hb x hx))
      (fun x hx => by rw [add_mul]; exact K'.add_mem (ha' x hx) (hb' x hx)) =
    idealQuotientLayerMul X α F hJ hK a ha ha' +
      idealQuotientLayerMul X α F hJ hK b hb hb' := by
  apply (cancel_mono (kernel.ι (idealQuotientMap X α F hK))).mp
  simp only [Preadditive.add_comp, idealQuotientLayerMul_ι]
  rw [← Preadditive.comp_add]
  exact congrArg (fun g => kernel.ι (idealQuotientMap X α F hJ) ≫ g)
    (idealQuotientMul_add X α F a b ha hb)

end AlgebraicGeometry.Scheme.Modules
