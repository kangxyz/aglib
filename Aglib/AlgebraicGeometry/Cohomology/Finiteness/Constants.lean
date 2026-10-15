/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Proper geometrically integral constants input

The explicit theorem-family predicate concerns bijectivity of the actual
structural constants map on proper geometrically integral field schemes. It
is retained as data, not proved here, and is separate from cohomology finiteness.

Source: `R5Lab.AlgebraicGeometry.Curves.Genus` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. Only ProperGeometricallyIntegralConstants, from the
  selected Genus lines 54–61.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme
universe u

/-- The general constants theorem in arbitrary dimension for proper
geometrically integral field schemes, stated for the actual canonical map.
Stacks 04L2 (33.26.2(4)), reducing to 33.9.3; statement, proof locator and
absence of correction comments inspected 2026-10-09. Retained general premise. -/
def ProperGeometricallyIntegralConstants : Prop :=
  ∀ (K : Type u) [Field K] (X : FScheme K), IsProper X.hom →
    GeometricallyIntegral X.hom → Function.Bijective (constants X)

end AlgebraicGeometry.Scheme
