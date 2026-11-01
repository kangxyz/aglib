/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Naturality

/-! Whole original-map consumers of flat naturality. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] {X₀ X₁ Y₀ Y₁ : FScheme k}
  (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) [Flat f.left] [Flat g.left]

example : Flat (f ⊗ₘ g).left := structureProduct_map_flat f g

example (n : ℕ) :
    structureCohomologyPullbackLinear (f ⊗ₘ g) n ∘ₗ structureKunnethMap X₁ Y₁ n =
      structureKunnethMap X₀ Y₀ n ∘ₗ structureKunnethSumPullback f g n :=
  structureKunnethMap_naturality f g n
