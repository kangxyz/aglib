/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.IrreducibleComponents.FiniteCover
public import Aglib.AlgebraicGeometry.Morphisms.Finite.Coproduct

/-!
# Finiteness of the original component coproduct map

The finite-index coproduct theorem applies to the original closed component
inclusions. Together with the lower component geometry, this gives an actual
finite surjective map which is an isomorphism on the separating open when
the original scheme is reduced. No field or dimension assumption is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IrreducibleComponentCover

variable (X : Scheme.{u}) [IsNoetherian X]

/-- The literal coproduct of all original closed component inclusions is finite. -/
instance map_finite : IsFinite (map X) := by
  let : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  exact isFinite_sigmaDesc (component X) (inclusion X)

end AlgebraicGeometry.Scheme.IrreducibleComponentCover
