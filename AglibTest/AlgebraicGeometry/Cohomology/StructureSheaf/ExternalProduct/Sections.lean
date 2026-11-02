/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Sections

/-! The H0 normalization uses all original global sections, without properness. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y : FScheme k)

example {n : ℕ} (x : Scheme.structureCohomology k X n)
    (y : Scheme.structureCohomology k Y 0) :
    structureExternalCup X Y (Nat.add_zero n) x y =
      Sheaf.H.map
        (moduleScalarOfGlobal (X ⊗ Y).left (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf)
          ((snd X Y).left.appTop (Scheme.structureH0Equiv Y y))) n
        (structureCohomologyPullbackLinear (fst X Y) n x) :=
  structureExternalCup_zero_right X Y x y
