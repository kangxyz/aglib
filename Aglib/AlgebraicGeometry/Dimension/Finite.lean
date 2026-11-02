/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Dimension does not increase under finite morphisms

The original public API is retained. The complete integral prime-chain and
affine-cover construction now lives uniquely in `Dimension.Integral`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite morphism does not increase topological Krull dimension.
Neither scheme is required to be Noetherian, reduced, nonempty, or of finite
dimension, and the morphism need not be surjective. -/
theorem Hom.topologicalKrullDim_le_of_isFinite
    {X Z : Scheme.{u}} (f : X ⟶ Z) [IsFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim Z :=
  f.topologicalKrullDim_le_of_isIntegralHom

end AlgebraicGeometry.Scheme
