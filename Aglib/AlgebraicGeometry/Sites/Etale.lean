/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Subcanonicity and continuous restriction for etale scheme sites

These are the original small-etale topology providers extracted from the
represented-coefficient construction. Their names, objects, maps and premises
are retained so general coefficients can use them before finite torsors.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- The actual big étale topology is subcanonical. -/
theorem etaleSubcanonical : Scheme.etaleTopology.{u}.Subcanonical :=
  .of_le Scheme.etaleTopology_le_proetaleTopology

attribute [local instance] etaleSubcanonical

/-- Restriction from schemes over `X` to étale test schemes is continuous. -/
instance smallEtaleForgetContinuous (X : Scheme.{u}) :
    (Scheme.Etale.forget X).IsContinuous (Scheme.smallEtaleTopology X)
      (Scheme.etaleTopology.over X) := by
  let := flat_of_preservesFiniteLimits (Scheme.Etale.forget X)
  exact Functor.isContinuous_iff_coverPreserving.mpr
    (Functor.coverPreserving_restrictedTopology
      (MorphismProperty.Over.forget @Etale ⊤ X) (Scheme.etaleTopology.over X))

/-- The actual small étale topology is subcanonical. -/
theorem smallEtaleSubcanonical (X : Scheme.{u}) :
    (Scheme.smallEtaleTopology X).Subcanonical :=
  GrothendieckTopology.subcanonical_of_full_of_faithful
    (Scheme.Etale.forget X) _ (Scheme.etaleTopology.over X)

end AlgebraicGeometry.Scheme.EtaleCohomology
