/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-! # Quasicoherence of the actual structure module -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual structure module is quasicoherent on every scheme. -/
theorem isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := by
  apply QuasiCoherent.quasicoherent_of_affineCharts
  intro R j _
  have h : (SheafOfModules.unit (Spec R).ringCatSheaf).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (restrictUnitIso j).symm h

end AlgebraicGeometry.Scheme.Modules
