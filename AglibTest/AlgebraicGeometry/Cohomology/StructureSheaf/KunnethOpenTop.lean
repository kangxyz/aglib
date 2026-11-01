/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenTop

/-! The original mixed top map has exactly the original global forward map. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y : FScheme k)

example {p q n : ℕ} (h : p + q = n) (x : structureCohomology k X p)
    (y : structureOpenCohomology Y ⊤ q) :
    structureOpenTopLinearEquiv (X ⊗ Y) n (structureExternalOpenCup X Y ⊤ h x y) =
      structureExternalCup X Y h x (structureOpenTopLinearEquiv Y q y) :=
  structureExternalOpenCup_top X Y h x y

example (n : ℕ) :
    (structureOpenTopLinearEquiv (X ⊗ Y) n).toLinearMap ∘ₗ structureOpenKunnethMap X Y ⊤ n =
      structureKunnethMap X Y n ∘ₗ (structureOpenTopSourceEquiv X Y n).toLinearMap :=
  structureOpenKunnethMap_top X Y n

example (n : ℕ) (h : Function.Bijective (structureOpenKunnethMap X Y ⊤ n)) :
    Function.Bijective (structureKunnethMap X Y n) :=
  structureKunnethMap_bijective_of_openTop X Y n h
