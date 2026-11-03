/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Cup.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Composition

/-!
# Whole linear pullback laws of original structure-sheaf cohomology

The already selected direct-sum pullback preserves composition and identity
without flatness, by the original degreewise cohomology maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped DirectSum

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- Whole unrestricted composition for the already selected direct-sum pullback. -/
theorem structureCohomologyAlgebraPullbackLinear_comp
    {X Y Z : FScheme k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureCohomologyAlgebraPullbackLinear (f ≫ g) =
      structureCohomologyAlgebraPullbackLinear f ∘ₗ
        structureCohomologyAlgebraPullbackLinear g := by
  apply DirectSum.linearMap_ext k
  intro n
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, structureCohomologyAlgebraPullbackLinear_inclusion,
    structureCohomologyPullbackLinear_comp]

/-- Whole identity for that same unrestricted original pullback. -/
theorem structureCohomologyAlgebraPullbackLinear_id (X : FScheme k) :
    structureCohomologyAlgebraPullbackLinear (𝟙 X) = LinearMap.id := by
  apply DirectSum.linearMap_ext k
  intro n
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, structureCohomologyAlgebraPullbackLinear_inclusion,
    structureCohomologyPullbackLinear_id, LinearMap.id_apply]

end AlgebraicGeometry.Scheme.Cohomology
