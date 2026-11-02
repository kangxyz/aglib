/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Original affine sections of the structure module

The native tilde/global-section comparison identifies the original unit sections with
the original scalar module. The existing qualified declaration is preserved.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {R : CommRingCat.{u}}

/-- Global sections of the structure sheaf of `Spec R` are `R`. -/
def globalSectionsUnitIso :
    moduleSpecΓFunctor.obj (SheafOfModules.unit (Spec R).ringCatSheaf) ≅ ModuleCat.of R R :=
  (tilde.toTildeΓNatIso.app (ModuleCat.of R R)).symm

end AlgebraicGeometry.Scheme.Modules.Invertible
