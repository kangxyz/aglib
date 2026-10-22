/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.ProperModification
public import Aglib.AlgebraicGeometry.Approximation.ClosedSubscheme.FiniteType

/-!
# Proper finite-presentation approximation from an actual ambient envelope

Given a closed embedding of the original proper scheme into a separated
finitely presented scheme over the same affine base, construct its actual
small proper FP approximation. The finite-type ideal system, its native limit,
the Chow modification, the proper stage, and the cofinal tail are all built
internally. The ambient envelope remains an explicit intermediate premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Approximation

/-- An actual closed separated-FP ambient envelope supplies a genuine proper
FP inverse system with the unchanged base, point, and closed projections.
All approximation stages and the proper modification are constructed. -/
theorem nonempty_properSystem_of_closed_finitePresentation_envelope
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f]
    (Y : Over S) [IsSeparated Y.hom] [LocallyOfFinitePresentation Y.hom]
    [QuasiCompact Y.hom] (i : X ⟶ Y.left) [IsClosedImmersion i]
    (hi : i ≫ Y.hom = f) : Nonempty (ProperFinitePresentationSystem f) := by
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let D := AlgebraicGeometry.Approximation.ClosedSubscheme.finitePresentationDiagram i
  let c := AlgebraicGeometry.Approximation.ClosedSubscheme.finitePresentationCone i
  exact nonempty_properSystem_of_closedApproximation f Y i hi D c
    (AlgebraicGeometry.Approximation.ClosedSubscheme.finitePresentationCone_pt i)
    (AlgebraicGeometry.Approximation.ClosedSubscheme.isLimitFinitePresentationCone i)

end AlgebraicGeometry.Scheme.Approximation
