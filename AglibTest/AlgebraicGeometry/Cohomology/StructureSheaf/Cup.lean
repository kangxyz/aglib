/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Cup

/-! The original cohomology cup unit is preserved by arbitrary geometric
pullback; the consumer has no flatness assumption on the morphism. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology

universe u

@[expose] public noncomputable section

variable {k : Type u} [Field k] {X Y : FScheme k}

example (f : X ⟶ Y) :
    structureCohomologyPullbackLinear f 0 (structureCupUnit Y) = structureCupUnit X :=
  structureCohomologyPullbackLinear_cupUnit X f

example (a : k) {n : ℕ} (x : Scheme.structureCohomology k X n) :
    structureCup X (Nat.zero_add n) (a • structureCupUnit X) x = a • x :=
  structureCup_smul_unit_left X a x
