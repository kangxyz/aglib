/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.RightProjection
public import Aglib.KTheory.MilnorK.Norm.Polynomial.One

/-! # The original finite-extension norm in degree one and on mixed products -/

@[expose] public noncomputable section

open Additive

namespace MilnorK

open PolynomialNorm

variable (k E : Type*) [Field k] [Field E] [Algebra k E]
  [Module.Finite k E] [CharZero k]

/-- The original finite-field Milnor norm is the determinant norm in degree one. -/
theorem oneEquiv_finiteExtensionNorm (x : K E 1) :
    oneEquiv k (finiteExtensionNorm k E 1 x) =
      ofMul (Units.map (Algebra.norm k) (oneEquiv E x).toMul) := by
  unfold finiteExtensionNorm
  rw [LinearMap.comp_apply, oneEquiv_polynomialNorm, oneEquiv_map]
  congr 1
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv (finiteNormPresentation k E).symm
    (oneEquiv E x).toMul

/-- The actual finite norm of a degree-one unit. -/
theorem finiteExtensionNorm_unitsToOne (b : Additive Eˣ) :
    finiteExtensionNorm k E 1 (unitsToOne E b) =
      unitsToOne k (ofMul (Units.map (Algebra.norm k) b.toMul)) := by
  apply (oneEquiv k).injective
  rw [oneEquiv_finiteExtensionNorm]
  change ofMul (Units.map (Algebra.norm k) ((oneEquiv E) ((oneEquiv E).symm b)).toMul) =
    (oneEquiv k) ((oneEquiv k).symm _)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Arbitrary base classes times one extension-field unit obey the genuine mixed norm law. -/
theorem finiteExtensionNorm_productUnit_constants (n : ℕ) (x : K k n) (b : Additive Eˣ) :
    finiteExtensionNorm k E (n + 1)
      (productUnit n (map n (algebraMap k E) x) b) =
        productUnit n x (ofMul (Units.map (Algebra.norm k) b.toMul)) := by
  change finiteExtensionNorm k E (n + 1)
    (product n 1 (map n (algebraMap k E) x) (unitsToOne E b)) = _
  rw [finiteExtensionNorm_product_constants_left, finiteExtensionNorm_unitsToOne]
  rfl

end MilnorK
