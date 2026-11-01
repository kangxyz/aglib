/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethAffine

/-! The affine antidiagonal reduction preserves the actual original map. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y : FScheme k) [IsAffine Y.left]

example (n : ℕ) :
    structureKunnethMap X Y n ∘ₗ (structureKunnethSumAffineEquiv X Y n).toLinearMap =
      structureExternalTensor X Y (Nat.add_zero n) :=
  structureKunnethMap_affine_equiv X Y n
