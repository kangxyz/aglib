/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Inverse composition form of the canonical pullback-unit comparison

The equation is obtained from the native composition comparison by cancellation
of its actual composition isomorphism. It uses arbitrary schemes and exactly
the original module pullback, unit maps and composition components.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The inverse composition component followed by the two unit maps is the composite unit map. -/
theorem pullbackUnitIso_comp_inv :
    (Scheme.Modules.pullbackComp f g).inv.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom =
        (pullbackUnitIso (f ≫ g)).hom :=
  ((Scheme.Modules.pullbackComp f g).app (SheafOfModules.unit Z.ringCatSheaf)).inv_comp_eq.mpr
    (pullbackUnitIso_comp f g).symm

end AlgebraicGeometry.Scheme.Modules
