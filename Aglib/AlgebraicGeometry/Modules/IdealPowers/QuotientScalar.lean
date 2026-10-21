/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.QuotientLayers

/-! # Degree-zero scalar compatibility of original quotient layers -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable (X : Scheme.{u}) {A : Type u} [CommRing A]
  (α : A →+* Γ(X, ⊤)) (F : X.Modules)

/-- With the same quotient on both sides, scalar-induced multiplication is
the original structural scalar endomorphism. -/
theorem idealQuotientMul_self (J : Ideal A) (a : A) :
    idealQuotientMul X α F a (fun _ hb => J.mul_mem_left a hb) =
      globalScalarEndomorphism X (idealQuotient X α F J) (α a) := by
  apply (cancel_epi (idealQuotientπ X α F J)).mp
  rw [idealQuotientπ_mul]
  exact ((globalScalarCenter X (α a)).naturality (idealQuotientπ X α F J)).symm

/-- The map on an unchanged quotient layer is its original structural scalar. -/
theorem idealQuotientLayerMul_self {J J' : Ideal A} (h : J ≤ J') (a : A) :
    idealQuotientLayerMul X α F h h a
      (fun _ hb => J.mul_mem_left a hb) (fun _ hb => J'.mul_mem_left a hb) =
      globalScalarEndomorphism X (idealQuotientLayer X α F h) (α a) := by
  apply (cancel_mono (kernel.ι (idealQuotientMap X α F h))).mp
  rw [idealQuotientLayerMul_ι, idealQuotientMul_self]
  exact (globalScalarCenter X (α a)).naturality (kernel.ι (idealQuotientMap X α F h))

end AlgebraicGeometry.Scheme.Modules
