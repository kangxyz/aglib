/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Properties.IrreducibleComponents.FiniteCoverFiniteness
public import Aglib.AlgebraicGeometry.Dimension.DenseOpenComplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Integral component covers and their lower-dimensional boundary

The actual finite surjective component coproduct of a reduced Noetherian
scheme is an isomorphism away from an explicitly produced closed subscheme
of lower dimension. Each original closed component has dimension bounded by
the original scheme and inherits properness over any original proper base.
For dimension at most one, taking `d = 0` gives the zero-dimensional boundary
needed by the curve cohomology descent argument. No field hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IrreducibleComponentCover

variable (X : Scheme.{u}) [IsNoetherian X]

/-- The original closed component has no larger topological dimension than the ambient scheme. -/
theorem component_topologicalKrullDim_le (c : irreducibleComponents X) :
    topologicalKrullDim (component X c) ≤ topologicalKrullDim X :=
  (inclusion X c).isClosedEmbedding.isInducing.topologicalKrullDim_le

/-- Every original component inherits properness over the unchanged base map. -/
theorem component_isProper {S : Scheme.{u}} (p : X ⟶ S) [IsProper p]
    (c : irreducibleComponents X) : IsProper (inclusion X c ≫ p) := by
  infer_instance

/-- The separating open has an actual closed boundary with the dimension lowered by one.
For a reduced scheme, the same open is the isomorphism locus supplied by the component cover. -/
theorem exists_closedBoundary (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range (separatingOpen X).ι = (Set.range i)ᶜ ∧
        topologicalKrullDim Z ≤ (d : ℕ) :=
  (separatingOpen X).ι.exists_closedComplement_topologicalKrullDim_le d hdim

end AlgebraicGeometry.Scheme.IrreducibleComponentCover
