/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Graded

/-! The signed algebra map has the original finite-degree external product. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y : FScheme k)

private abbrev structureExternalAlgebraMap_tmul_test {p q n : ℕ} (h : p + q = n)
    (x : Scheme.structureCohomology k X p) (y : Scheme.structureCohomology k Y q) :=
  (structureExternalAlgebraMap_tmul X Y h x y).trans
    (congrArg (structureCohomologyInclusion (X ⊗ Y) n)
      (structureExternalTensor_tmul X Y h x y).symm)

private abbrev structureExternalAlgebraMap_mul_test :=
  map_mul (structureExternalAlgebraMap X Y)

example : structureExternalTensorSourceEquiv X Y
    ((1 : structureCohomologyAlgebra X) ⊗ₜ[k] (1 : structureCohomologyAlgebra Y)) = 1 :=
  structureExternalTensorSourceEquiv_one X Y

private abbrev structureExternalAlgebraMap_tensor_test {p q n : ℕ} (h : p + q = n)
    (x : Scheme.structureCohomology k X p) (y : Scheme.structureCohomology k Y q) :=
  LinearMap.congr_fun (structureExternalAlgebraMap_tensor X Y h) (x ⊗ₜ[k] y)
