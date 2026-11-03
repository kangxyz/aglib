/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Values

/-! The original signed forward map uses the one canonical linear comparison. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y : FScheme k)

private abbrev structureExternalLinearMap_signed_test
    (z : structureCohomologyAlgebra X ⊗[k] structureCohomologyAlgebra Y) :=
  LinearMap.congr_fun (structureExternalLinearMap_signed X Y) z

example {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y q) :
    structureExternalLinearMap X Y
        (structureCohomologyInclusion X p x ⊗ₜ[k] structureCohomologyInclusion Y q y) =
      structureCohomologyInclusion (X ⊗ Y) n (structureExternalCup X Y h x y) :=
  structureExternalLinearMap_tmul X Y h x y

variable
  [QuasiCompact X.hom] [QuasiSeparated X.hom]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

private abbrev structureExternalAlgebraMap_linear_test
    (z : structureCohomologyAlgebra X ⊗[k] structureCohomologyAlgebra Y) :=
  LinearMap.congr_fun (structureExternalAlgebraMap_linear X Y) z
