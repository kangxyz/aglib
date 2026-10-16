/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.StructureSheaf
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation

/-!
# The proved field-scheme proper finiteness suppliers

The unconditional Noetherian-base theorem supplies the retained all-field
proper module-cohomology family. Its original scalar action specializes
literally to the existing field action. The original structure-module
comparison then supplies structure-sheaf finiteness, and the original
H0 comparison supplies finite global sections. No theorem-family premise
is passed to these public suppliers.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Proper finiteness in every degree for every finitely presented coefficient
on every field scheme, with the original structural field action. -/
theorem properModuleCohomologyFinite : ProperModuleCohomologyFinite.{u} := by
  intro K _ X M n hX hM
  let := hX
  let := hM
  exact moduleCohomology_finite_of_proper K X.hom M
    (affineLocallyFiniteType_of_finitePresentation M) n

/-- The retained structure-sheaf family is supplied by the actual proper
module theorem and its original scalar-compatible structure comparison. -/
theorem properStructureCohomologyFinite : ProperStructureCohomologyFinite.{u} :=
  properStructureCohomologyFinite_of_standard properModuleCohomologyFinite

/-- Actual global sections of a finitely presented coefficient on a proper
field scheme are finite, through the original H0 equivalence. -/
theorem moduleGlobalSections_finite_of_proper {K : Type u} [Field K]
    (X : FScheme K) (M : X.left.Modules) (hX : IsProper X.hom)
    (hM : M.IsFinitePresentation) :
    Module.Finite K (M.val.obj (Opposite.op ⊤)) :=
  moduleGlobalSections_finite properModuleCohomologyFinite X M hX hM

end AlgebraicGeometry.Scheme.Cohomology
