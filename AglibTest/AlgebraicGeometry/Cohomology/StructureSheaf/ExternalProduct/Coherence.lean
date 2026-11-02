/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Coherence

/-! The original external maps use the native associator and signed swap. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y Z : FScheme k)

example (p q r : ℕ) (x : Scheme.structureCohomology k X p)
    (y : Scheme.structureCohomology k Y q) (z : Scheme.structureCohomology k Z r) :
    structureCohomologyPullbackLinear (α_ X Y Z).hom (p + q + r)
        (structureExternalCup X (Y ⊗ Z) (Nat.add_assoc p q r).symm x
          (structureExternalCup Y Z rfl y z)) =
      structureExternalCup (X ⊗ Y) Z rfl (structureExternalCup X Y rfl x y) z :=
  structureExternalCup_assoc X Y Z rfl rfl rfl x y z

example {p q n : ℕ} (h : p + q = n)
    (x : Scheme.structureCohomology k X p) (y : Scheme.structureCohomology k Y q) :
    structureExternalCup X Y h x y = ((-1 : ℤ) ^ (p * q)) •
      structureCohomologyPullbackLinear (β_ X Y).hom n
        (structureExternalCup Y X ((Nat.add_comm q p).trans h) y x) :=
  structureExternalCup_symmetry X Y h x y
