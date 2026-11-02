/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-! # Original sections of the pulled-back structure module

The native pullback-unit isomorphism identifies sections of its direct image
with the original source structure-ring sections. Its original adjunction
unit is exactly the original scheme map on global sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The original pullback-unit comparison on the original global section carriers. -/
def pullbackUnitGlobalSectionsEquiv :
    Γ((pushforward f).obj ((pullback f).obj (SheafOfModules.unit X.ringCatSheaf)), ⊤) ≃
      Γ(Y, ⊤) :=
  ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso
    ((pushforward f).mapIso (pullbackUnitIso f))).toLinearEquiv.toEquiv

/-- The complete original unit formula, without introducing a ring on a quotient module. -/
theorem pullbackUnitGlobalSectionsEquiv_unit (r : Γ(X, ⊤)) :
    pullbackUnitGlobalSectionsEquiv f
        (Hom.app ((pullbackPushforwardAdjunction f).unit.app
          (SheafOfModules.unit X.ringCatSheaf)) ⊤ r) = f.appTop r := by
  have h := pullbackUnitIso_homEquiv f
  have hv := congrArg (fun k : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) => Hom.app k ⊤ r) h
  exact hv

end AlgebraicGeometry.Scheme.Modules
