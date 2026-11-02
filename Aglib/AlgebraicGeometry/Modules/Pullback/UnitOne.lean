/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-! # The original structure-module pullback unit on one -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- The original structure-module pullback unit sends the original unit section to one. -/
theorem pullbackUnitIso_unit_one :
    (Modules.pullbackUnitIso p).hom.app ⊤
      (((Modules.pullbackPushforwardAdjunction p).unit.app
        (SheafOfModules.unit X.ringCatSheaf)).app ⊤ (1 : Γ(X, ⊤))) =
      (1 : Γ(Y, ⊤)) := by
  have hu := Modules.pullbackUnitIso_homEquiv p
  change (Modules.pullbackPushforwardAdjunction p).unit.app
      (SheafOfModules.unit X.ringCatSheaf) ≫
        (Modules.pushforward p).map (Modules.pullbackUnitIso p).hom =
      SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom at hu
  have hv := congrArg (fun k => k.app ⊤ (1 : Γ(X, ⊤))) hu
  exact hv.trans (map_one (p.app ⊤).hom)

end AlgebraicGeometry.Scheme.Cohomology
