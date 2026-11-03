/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear

/-! The original total operator and its one canonical inverse on native cohomology. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology
open scoped TensorProduct DirectSum

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

example {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y q) :
    structureExternalLinearMap X Y
        (structureCohomologyInclusion X p x ⊗ₜ[k] structureCohomologyInclusion Y q y) =
      structureCohomologyInclusion (X ⊗ Y) n (structureExternalCup X Y h x y) :=
  structureExternalLinearMap_tmul X Y h x y

variable [QuasiCompact X.hom] [QuasiSeparated X.hom]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

example : (structureExternalLinearEquiv X Y).toLinearMap = structureExternalLinearMap X Y :=
  structureExternalLinearEquiv_toLinearMap X Y

example (n : ℕ) (z : structureCohomology k (X ⊗ Y) n) :
    (structureExternalLinearEquiv X Y).symm (structureCohomologyInclusion (X ⊗ Y) n z) =
      (structureTensorTotalSourceEquiv X Y).symm
        (DirectSum.lof k ℕ _ n ((structureKunnethDegreeEquiv X Y n).symm z)) :=
  structureExternalLinearEquiv_symm_inclusion X Y n z
