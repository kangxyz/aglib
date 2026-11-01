/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethAffineComparison

/-! The original affine external and antidiagonal maps, with no properness
or finite-type premise and no field structure on the affine global ring. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology
open scoped TensorProduct

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)
  [QuasiCompact X.hom] [QuasiSeparated X.hom] [IsAffine Y.left]

example (n : ℕ) :
    Function.Bijective (structureExternalTensor X Y (Nat.add_zero n)) :=
  structureExternalTensor_bijective_of_isAffine X Y n

example (n : ℕ) : Function.Bijective (structureKunnethMap X Y n) :=
  structureKunnethMap_bijective_of_isAffine X Y n

example (n : ℕ) :
    (fun z : structureCohomology k X n ⊗[k] structureCohomology k Y 0 =>
      structureAffineTensorMap X Y n (structureAffineSourceEquiv X Y n z)) =
      fun z => structureExternalTensor X Y (Nat.add_zero n) z :=
  structureAffineTensorMap_sourceEquiv X Y n

end
