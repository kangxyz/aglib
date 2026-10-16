/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Locality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteType
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic

/-!
# Finite presentation implies affine-locally finite-type quasicoherence

This direction is valid on arbitrary schemes and uses the actual finite
generator data, without a Noetherian hypothesis.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- Finite presentation implies finite-type quasicoherence on all affine
charts. No Noetherian hypothesis is required. -/
theorem affineLocallyFiniteType_of_finitePresentation {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] : affineLocallyFiniteType X M := by
  intro R j _
  have := finitePresentation_restrict j M
  exact ⟨inferInstance, Scheme.Modules.finite_globalSections_of_finitePresentation R _⟩

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
