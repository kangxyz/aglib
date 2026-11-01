/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom

/-! # The original structure-linear dual sheaf

The existing dual realization is shared by arbitrary module sheaves and line bundles.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable (X : Scheme.{u})

/-- The structure-linear internal-Hom sheaf from M to the structure-module unit. -/
def dualSheaf (M : SheafOfModules.{u} X.ringCatSheaf) : SheafOfModules.{u} X.ringCatSheaf :=
  InternalHom.sheaf X M (SheafOfModules.unit X.ringCatSheaf)

end AlgebraicGeometry.Scheme.Modules.Invertible
