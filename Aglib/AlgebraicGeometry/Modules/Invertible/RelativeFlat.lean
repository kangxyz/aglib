/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Tensor
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Unit

/-! # Original line bundles are relatively flat over a flat morphism

Use the actual local unit charts and native tensor unit comparison. No
Noetherianity, properness, or independent relative-flatness certificate is
needed for the line bundle. This supplies actual flatness of the graph-family
coefficients used in coherent semicontinuity arguments.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Tensoring with an actual line bundle preserves relative flatness. -/
theorem relativeFlat_tensor {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
    (M : X.Modules) (hM : relativeFlat f M) :
    relativeFlat f ((moduleTensorLeftFunctor X L.val).obj M) :=
  relativeFlat_tensor_of_locallyTrivial f L.val M
    ((isLocallyRankOne_iff_restrict_unit L.val).mp L.property) hM

/-- Every original line bundle on the source of a flat morphism is relatively flat. -/
theorem relativeFlat_of_flat {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (L : LineBundle X) : relativeFlat f L.val :=
  relativeFlat_of_iso f ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app L.val).symm
    (relativeFlat_tensor f L (SheafOfModules.unit X.ringCatSheaf)
      (relativeFlat_unit_of_flat f))

end AlgebraicGeometry.Scheme.Modules.Invertible
