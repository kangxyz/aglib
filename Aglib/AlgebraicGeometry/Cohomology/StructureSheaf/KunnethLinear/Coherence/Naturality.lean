/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Coherence.NaturalityData

/-!
# Naturality of the original total Kunneth operator

The chosen native operator has the original homogeneous values, product
naturality and associativity. Original unrestricted pullback laws are imported
from their lower owner before group coalgebra assembly.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct DirectSum

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The entire original total operator has flat geometric naturality. -/
abbrev structureExternalLinearMap_naturality
    {X₀ X₁ Y₀ Y₁ : FScheme k} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁)
    [Flat f.left] [Flat g.left] :=
  let h := structureExternalNaturalityInputs_mapIdentifications f g
  DirectSum.NaturalityInputs.diagramOfMapIdentifications h

end AlgebraicGeometry.Scheme.Cohomology
