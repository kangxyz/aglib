/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Noetherian
public import Aglib.AlgebraicGeometry.Group.Dimension
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Original coherent-cohomology vanishing above the group dimension

For a proper smooth geometrically integral group over any field, the actual
structure-sheaf cohomology vanishes beyond the dimension of its identity
cotangent space. This is the original `Sheaf.H` with its structural field action.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : FScheme k) [GrpObj G]
  [IsProper G.hom] [Smooth G.hom] [GeometricallyIntegral G.hom]

/-- Above the identity cotangent dimension, the original coherent cohomology
has only its zero class. -/
theorem structureCohomology_subsingleton_of_finrank_identityCotangent_lt
    (n : ℕ) (hn : Module.finrank k (Cotangent.Space η[G]) < n) :
    Subsingleton (structureCohomology k G n) := by
  let : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  let : CompactSpace G.left := (quasiCompact_iff_compactSpace G.hom).mp inferInstance
  let : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  let : IsNoetherian G.left := ⟨⟩
  have hdim : topologicalKrullDim G.left ≤
      Module.finrank k (Cotangent.Space η[G]) := by
    rw [topologicalKrullDim_eq_finrank_identityCotangent_of_preconnected G]
  exact noetherianSheafCohomology_vanishing G.left (structureAddSheaf G.left)
    (Module.finrank k (Cotangent.Space η[G])) n hdim hn

end AlgebraicGeometry.Scheme.Group
